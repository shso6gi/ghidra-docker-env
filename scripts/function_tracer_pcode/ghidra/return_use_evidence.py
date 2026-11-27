# -*- coding: utf-8 -*-
"""How the callers of a function in the same binary use its return registers (Issue #327, E-b).

For each direct call to the function's entry, the straight-line code after the
call is read as raw instruction P-code (never the decompiler, whose output is
built from the callee's *recovered* prototype), and a backward bit-level
analysis finds which bits of the return registers the caller's code really
**demands**: bits that reach a conditional branch, a comparison, a division,
a floating-point operation or the arithmetic feeding them.

The analysis is exact or under-approximating, so a demanded bit is one the
caller depends on along that path:

* constants computed in temporaries are folded first (the processor
  specifications compute shift amounts and masks that way);
* a STORE is a copy, never a sink: copying a register to memory copies its
  undefined bits too (the padding of a small aggregate).  Demand flows through
  memory only from a later LOAD of the same stack slot (a stack or frame
  register plus a constant, with no write to that register in between); a
  STORE to any other address forgets every tracked slot;
* an op whose meaning is not modelled demands nothing; so does a value that
  leaves the region (returned by the caller, passed to another call).

The record also says whether the callee's **own instructions** write each
return register (a call inside the callee does not count: with interprocedural
register allocation the caller knows which registers that call preserves), and,
per RETURN of the callee, the value width its return register is limited to by
the producer in the same block (an extension, a mask, a comparison result).

What this evidence does and does not show is decided by the consumer
(``concrete.observation_claim``); this module only reads the program.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

RETURN_USE_EVIDENCE_VERSION = "return-use-evidence-v1"

#: registers whose value plus a constant is a stack slot (AArch64 / MIPS)
STACK_BASE_REGISTERS = frozenset({"sp", "x29", "s8", "fp"})
#: bounds of one scan (a scan that hits them says so; the consumer treats a
#: truncated scan as evidence only of what it saw)
MAX_CALLSITES = 32
MAX_REGION_INSTRUCTIONS = 96

CONST = "const"


@dataclass(frozen=True)
class Vn:
    """A varnode: ``space`` is the address-space name (``const`` for a
    constant, whose value is ``offset``); ``register`` names a register."""

    space: str
    offset: int
    size: int
    register: Optional[str] = None

    @property
    def is_constant(self) -> bool:
        return self.space == CONST


@dataclass(frozen=True)
class Op:
    mnemonic: str
    output: Optional[Vn]
    inputs: Tuple[Vn, ...]


def _full(size: int) -> int:
    return (1 << (8 * size)) - 1


def prefix_bits(mask: int) -> int:
    """Length of the run of set bits from bit 0."""
    n = 0
    while (mask >> n) & 1:
        n += 1
    return n


def _overlap(a_space: str, a_off: int, a_size: int, b: Vn) -> bool:
    return a_space == b.space and a_off < b.offset + b.size and b.offset < a_off + a_size


class _Bits:
    """Demand per byte of a space: ``(space, byte address) -> 8-bit mask``."""

    def __init__(self, big_endian: bool):
        self._m: Dict[Tuple[str, int], int] = {}
        self._be = big_endian

    def _bytes(self, vn: Vn):
        for i in range(vn.size):  # i = significance of the byte
            yield i, (vn.space, vn.offset + (vn.size - 1 - i) if self._be else vn.offset + i)

    def get(self, vn: Vn) -> int:
        if vn.is_constant:
            return 0
        value = 0
        for i, key in self._bytes(vn):
            value |= self._m.get(key, 0) << (8 * i)
        return value

    def add(self, vn: Vn, mask: int) -> None:
        if vn.is_constant or not mask:
            return
        for i, key in self._bytes(vn):
            b = (mask >> (8 * i)) & 0xFF
            if b:
                self._m[key] = self._m.get(key, 0) | b

    def kill(self, vn: Vn) -> None:
        if vn.is_constant:
            return
        for _, key in self._bytes(vn):
            self._m.pop(key, None)


_FOLD = {
    "COPY": lambda a: a[0], "INT_ADD": lambda a: a[0] + a[1], "INT_SUB": lambda a: a[0] - a[1],
    "INT_MULT": lambda a: a[0] * a[1], "INT_LEFT": lambda a: a[0] << a[1], "INT_RIGHT": lambda a: a[0] >> a[1],
    "INT_AND": lambda a: a[0] & a[1], "INT_OR": lambda a: a[0] | a[1], "INT_XOR": lambda a: a[0] ^ a[1],
    "INT_ZEXT": lambda a: a[0], "INT_NEGATE": lambda a: ~a[0], "INT_2COMP": lambda a: -a[0],
}


def fold_constants(ops: Sequence[Op]) -> List[Tuple[Optional[int], ...]]:
    """Per op, the constant value of each input or ``None`` (forward over the
    straight-line region; any write to an overlapping location forgets a value)."""
    known: Dict[Tuple[str, int, int], int] = {}
    result: List[Tuple[Optional[int], ...]] = []
    for op in ops:
        values = tuple(
            vn.offset if vn.is_constant else known.get((vn.space, vn.offset, vn.size)) for vn in op.inputs
        )
        result.append(values)
        out = op.output
        if out is None:
            continue
        for key in [k for k in known if k[0] == out.space and k[1] < out.offset + out.size and out.offset < k[1] + k[2]]:
            known.pop(key)
        fn = _FOLD.get(op.mnemonic)
        if fn is not None and values and all(v is not None for v in values):
            try:
                known[(out.space, out.offset, out.size)] = fn(values) & _full(out.size)
            except (ValueError, OverflowError):
                pass
    return result


def _address_symbols(ops: Sequence[Op], folded) -> List[Optional[Tuple[str, int, int]]]:
    """Per op, the symbolic address ``(stack register, version, offset)`` of a
    LOAD / STORE when it is a stack register plus a constant, else ``None``."""
    version: Dict[str, int] = {}
    symbol: Dict[Tuple[str, int, int], Tuple[str, int, int]] = {}
    out: List[Optional[Tuple[str, int, int]]] = []

    def sym(vn: Vn):
        if vn.register in STACK_BASE_REGISTERS:
            return (vn.register, version.get(vn.register, 0), 0)
        return symbol.get((vn.space, vn.offset, vn.size))

    for index, op in enumerate(ops):
        address = sym(op.inputs[1]) if op.mnemonic in ("LOAD", "STORE") and len(op.inputs) > 1 else None
        out.append(address)
        o = op.output
        if o is None:
            continue
        value = None
        if op.mnemonic == "COPY":
            value = sym(op.inputs[0])
        elif op.mnemonic in ("INT_ADD", "INT_SUB") and len(op.inputs) == 2:
            base, c = sym(op.inputs[0]), folded[index][1]
            if base is not None and c is not None:
                c = c - (1 << (8 * op.inputs[1].size)) if c >> (8 * op.inputs[1].size - 1) else c
                value = (base[0], base[1], base[2] + (c if op.mnemonic == "INT_ADD" else -c))
        if o.register is not None:
            version[o.register] = version.get(o.register, 0) + 1
        symbol.pop((o.space, o.offset, o.size), None)
        if value is not None:
            symbol[(o.space, o.offset, o.size)] = value
    return out


_COMPARE = frozenset({
    "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL",
    "INT_CARRY", "INT_SCARRY", "INT_SBORROW", "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS",
    "FLOAT_LESSEQUAL", "FLOAT_NAN",
})
_WHOLE_INPUT = frozenset({
    "INT_DIV", "INT_SDIV", "INT_REM", "INT_SREM", "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV",
    "FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT", "FLOAT_INT2FLOAT", "FLOAT_FLOAT2FLOAT", "FLOAT_TRUNC",
    "FLOAT_CEIL", "FLOAT_FLOOR", "FLOAT_ROUND", "POPCOUNT", "BOOL_NEGATE", "BOOL_AND", "BOOL_OR", "BOOL_XOR",
}) | _COMPARE
_CARRY_UP = frozenset({"INT_ADD", "INT_SUB", "INT_MULT", "INT_2COMP"})


def demanded_bits(ops: Sequence[Op], big_endian: bool) -> _Bits:
    """Backward demand over the straight-line region ``ops``: the bits each
    location holds at the region start that the region's sinks depend on."""
    demand = _Bits(big_endian)
    folded = fold_constants(ops)
    symbols = _address_symbols(ops, folded)
    memory: Dict[Tuple[str, int, int], int] = {}

    def slot(address, size):
        for i in range(size):
            yield i, (address[0], address[1], address[2] + ((size - 1 - i) if big_endian else i))

    for index in range(len(ops) - 1, -1, -1):
        op = ops[index]
        name, out, ins, consts = op.mnemonic, op.output, op.inputs, folded[index]
        if name == "STORE":
            address, value = symbols[index], ins[2]
            if address is None:
                memory.clear()
            else:
                mask = 0
                for i, key in slot(address, value.size):
                    mask |= memory.pop(key, 0) << (8 * i)
                demand.add(value, mask)
            continue
        if name == "CBRANCH":
            demand.add(ins[1], _full(ins[1].size))
            continue
        if out is None:
            continue
        d = demand.get(out)
        demand.kill(out)
        if not d:
            continue
        if name == "LOAD":
            address = symbols[index]
            if address is not None:
                for i, key in slot(address, out.size):
                    b = (d >> (8 * i)) & 0xFF
                    if b:
                        memory[key] = memory.get(key, 0) | b
        elif name == "COPY":
            demand.add(ins[0], d)
        elif name == "INT_ZEXT":
            demand.add(ins[0], d & _full(ins[0].size))
        elif name == "INT_SEXT":
            n = ins[0].size
            demand.add(ins[0], d & _full(n))
            if d >> (8 * n):
                demand.add(ins[0], 1 << (8 * n - 1))
        elif name == "SUBPIECE":
            shift = consts[1] or 0
            demand.add(ins[0], (d << (8 * shift)) & _full(ins[0].size))
        elif name == "PIECE":
            low = ins[1].size
            demand.add(ins[1], d & _full(low))
            demand.add(ins[0], (d >> (8 * low)) & _full(ins[0].size))
        elif name == "INT_AND":
            if consts[1] is not None:
                demand.add(ins[0], d & consts[1])
            elif consts[0] is not None:
                demand.add(ins[1], d & consts[0])
            else:
                demand.add(ins[0], d)
                demand.add(ins[1], d)
        elif name in ("INT_OR", "INT_XOR"):
            for i, vn in enumerate(ins):
                if consts[i] is None:
                    demand.add(vn, d)
        elif name == "INT_NEGATE":
            demand.add(ins[0], d)
        elif name in _CARRY_UP:
            low = (1 << d.bit_length()) - 1
            for i, vn in enumerate(ins):
                if consts[i] is None:
                    demand.add(vn, low & _full(vn.size))
        elif name == "INT_LEFT":
            if consts[1] is not None:
                demand.add(ins[0], d >> consts[1])
            else:
                demand.add(ins[0], _full(ins[0].size))
                demand.add(ins[1], _full(ins[1].size))
        elif name in ("INT_RIGHT", "INT_SRIGHT"):
            n = ins[0].size
            if consts[1] is not None:
                demand.add(ins[0], (d << consts[1]) & _full(n))
                if name == "INT_SRIGHT" and d >> max(0, 8 * n - consts[1]):
                    demand.add(ins[0], 1 << (8 * n - 1))
            else:
                demand.add(ins[0], _full(n))
                demand.add(ins[1], _full(ins[1].size))
        elif name in _WHOLE_INPUT:
            for i, vn in enumerate(ins):
                if consts[i] is None:
                    demand.add(vn, _full(vn.size))
        # anything else (CALLOTHER, MULTIEQUAL, ...): no definite demand
    return demand


def own_write(ops: Iterable[Op], register: Vn) -> bool:
    """Whether one of ``ops`` (the callee's own instructions) writes ``register``."""
    return any(op.output is not None and _overlap(op.output.space, op.output.offset, op.output.size, register)
               for op in ops)


def producer_limit(block_ops: Sequence[Op], index: int, vn: Vn, depth: int = 0) -> Optional[int]:
    """Value-width limit (bits) of ``vn`` as defined before ``block_ops[index]``
    inside the block: an extension, a mask ``2^n-1``, a comparison result, a
    narrow load.  ``None`` when the defining op is outside the block."""
    if depth > 12:
        return None
    for j in range(index - 1, -1, -1):
        op = block_ops[j]
        o = op.output
        if o is None or not _overlap(o.space, o.offset, o.size, vn):
            continue
        if o.offset != vn.offset or o.size < vn.size:
            return 8 * vn.size
        name, ins = op.mnemonic, op.inputs
        if name == "COPY":
            if ins[0].is_constant:
                return max(1, ins[0].offset.bit_length())
            return producer_limit(block_ops, j, ins[0], depth + 1)
        if name in ("INT_ZEXT", "INT_SEXT") or (name == "SUBPIECE" and ins[1].is_constant and ins[1].offset == 0):
            width = 8 * (ins[0].size if name != "SUBPIECE" else o.size)
            inner = producer_limit(block_ops, j, ins[0], depth + 1)
            return width if inner is None else min(width, inner)
        if name == "INT_AND":
            c = ins[1].offset if ins[1].is_constant else (ins[0].offset if ins[0].is_constant else None)
            if c is not None and c >= 0 and (c & (c + 1)) == 0:
                return max(1, c.bit_length())
            return 8 * vn.size
        if name in _COMPARE or name.startswith("BOOL_"):
            return 1
        if name == "LOAD":
            return 8 * o.size
        return 8 * vn.size
    return None


# ------------------------------------------------------------------ records

@dataclass(frozen=True)
class CallsiteDemand:
    """One direct call to the function: where, how the straight-line region
    after it ended, and the demanded bits of each return register class."""

    call_address: int
    caller_entry: Optional[int]
    region_end: str
    demand: Tuple[Tuple[str, int], ...]

    def demanded(self, value_class: str) -> int:
        return dict(self.demand).get(value_class, 0)

    def to_json(self) -> Mapping[str, Any]:
        return {"call": self.call_address, "caller": self.caller_entry, "end": self.region_end,
                "demand": {k: v for k, v in self.demand}}


@dataclass(frozen=True)
class ReturnUseEvidence:
    """What the callers of one function do with its return registers.

    ``status``: ``SCANNED`` (the function was found and every call reference
    was read, up to ``MAX_CALLSITES``), ``NO_FUNCTION``, ``STOPPED`` (the
    caller's stop condition fired: the scan is incomplete), ``FAILED`` (reading
    the program raised; ``detail`` says what).  Only ``SCANNED`` is evidence.
    """

    status: str
    registers: Tuple[Tuple[str, str], ...] = ()
    detail: str = ""
    own_writes: Tuple[Tuple[str, bool], ...] = ()
    callsites: Tuple[CallsiteDemand, ...] = ()
    callsites_truncated: bool = False
    return_path_limits: Tuple[Tuple[str, Tuple[Optional[int], ...]], ...] = ()
    version: str = RETURN_USE_EVIDENCE_VERSION

    def to_json(self) -> Mapping[str, Any]:
        return {
            "version": self.version,
            "status": self.status,
            "detail": self.detail,
            "registers": {k: v for k, v in self.registers},
            "own_writes": {k: v for k, v in self.own_writes},
            "callsites": [c.to_json() for c in self.callsites],
            "callsites_truncated": self.callsites_truncated,
            "return_path_limits": {k: list(v) for k, v in self.return_path_limits},
        }


# ------------------------------------------------------------------ Ghidra

def _vn(varnode: Any, language: Any) -> Vn:
    address = varnode.getAddress()
    space = str(address.getAddressSpace().getName())
    if varnode.isConstant():
        return Vn(CONST, int(varnode.getOffset()), int(varnode.getSize()))
    register = None
    if varnode.isRegister():
        reg = language.getRegister(address, int(varnode.getSize()))
        register = str(reg.getName()) if reg is not None else None
    return Vn(space, int(varnode.getOffset()), int(varnode.getSize()), register)


def _ops(pcode: Iterable[Any], language: Any) -> List[Op]:
    out = []
    for p in pcode:
        o = p.getOutput()
        out.append(Op(str(p.getMnemonic()), None if o is None else _vn(o, language),
                      tuple(_vn(p.getInput(i), language) for i in range(p.getNumInputs()))))
    return out


def _straight_region(listing: Any, start: Any, language: Any) -> Tuple[List[Op], str]:
    ops: List[Op] = []
    instruction, count, end = start, 0, "LIMIT"
    while instruction is not None and count < MAX_REGION_INSTRUCTIONS:
        if count == 0 and instruction.isInDelaySlot():
            instruction = instruction.getNext()
            continue
        pcode = _ops(instruction.getPcode(), language)
        ops.extend(pcode)
        count += 1
        names = {op.mnemonic for op in pcode}
        if "RETURN" in names:
            end = "RETURN"; break
        if names & {"CALL", "CALLIND"}:
            end = "CALL"; break
        if names & {"BRANCH", "BRANCHIND"}:
            end = "BRANCH"; break
        if "CBRANCH" in names:
            end = "CBRANCH"; break
        following = instruction.getFallThrough()
        if following is None:
            end = "NO_FALLTHROUGH"; break
        instruction = listing.getInstructionAt(following)
    return ops, end


def scan_return_use(
    program: Any,
    entry_offset: int,
    register_names: Mapping[str, str],
    *,
    should_stop: Callable[[], bool] = lambda: False,
) -> ReturnUseEvidence:
    """Read the callers of the function at ``entry_offset`` (``register_names``
    maps a value class, ``INT`` / ``FP``, to the ABI return register's name)."""
    from ghidra.program.model.block import SimpleBlockModel  # noqa: PLC0415
    from ghidra.util.task import TaskMonitor  # noqa: PLC0415

    language = program.getLanguage()
    big_endian = bool(language.isBigEndian())
    listing = program.getListing()
    functions = program.getFunctionManager()
    entry = program.getAddressFactory().getDefaultAddressSpace().getAddress(int(entry_offset))
    function = functions.getFunctionAt(entry)
    registers = tuple(sorted(register_names.items()))
    if function is None or function.isExternal() or function.isThunk():
        return ReturnUseEvidence("NO_FUNCTION", registers)
    reg_vn: Dict[str, Vn] = {}
    for value_class, name in registers:
        reg = language.getRegister(name)
        reg_vn[value_class] = Vn(str(reg.getAddress().getAddressSpace().getName()), int(reg.getAddress().getOffset()),
                                 int(reg.getMinimumByteSize()), name)

    body: List[Op] = []
    limits: Dict[str, List[Optional[int]]] = {k: [] for k in reg_vn}
    blocks = SimpleBlockModel(program)
    for instruction in listing.getInstructions(function.getBody(), True):
        if should_stop():
            return ReturnUseEvidence("STOPPED", registers)
        pcode = _ops(instruction.getPcode(), language)
        body.extend(pcode)
        if any(op.mnemonic == "RETURN" for op in pcode):
            block = blocks.getFirstCodeBlockContaining(instruction.getAddress(), TaskMonitor.DUMMY)
            block_ops: List[Op] = []
            for item in listing.getInstructions(block, True):
                if item.getAddress().compareTo(instruction.getAddress()) > 0:
                    break
                block_ops.extend(_ops(item.getPcode(), language))
            index = next(i for i, op in enumerate(block_ops) if op.mnemonic == "RETURN")
            for value_class, vn in reg_vn.items():
                limits[value_class].append(producer_limit(block_ops, index, vn))
    own = tuple((k, own_write(body, vn)) for k, vn in sorted(reg_vn.items()))

    callsites: List[CallsiteDemand] = []
    truncated = False
    references = sorted(
        (ref for ref in program.getReferenceManager().getReferencesTo(entry) if ref.getReferenceType().isCall()),
        key=lambda ref: int(ref.getFromAddress().getOffset()),
    )
    for ref in references:
        if should_stop():
            return ReturnUseEvidence("STOPPED", registers)
        if len(callsites) >= MAX_CALLSITES:
            truncated = True
            break
        call = listing.getInstructionAt(ref.getFromAddress())
        if call is None or not call.getFlowType().isCall():
            continue
        caller = functions.getFunctionContaining(ref.getFromAddress())
        following = call.getFallThrough()
        start = listing.getInstructionAt(following) if following is not None else None
        if start is None:
            callsites.append(CallsiteDemand(int(ref.getFromAddress().getOffset()),
                                            None if caller is None else int(caller.getEntryPoint().getOffset()),
                                            "TAIL_CALL", tuple((k, 0) for k in sorted(reg_vn))))
            continue
        region, end = _straight_region(listing, start, language)
        demand = demanded_bits(region, big_endian)
        callsites.append(CallsiteDemand(
            int(ref.getFromAddress().getOffset()),
            None if caller is None else int(caller.getEntryPoint().getOffset()),
            end, tuple((k, demand.get(vn)) for k, vn in sorted(reg_vn.items())),
        ))
    return ReturnUseEvidence(
        "SCANNED", registers=registers, own_writes=own, callsites=tuple(callsites), callsites_truncated=truncated,
        return_path_limits=tuple((k, tuple(v)) for k, v in sorted(limits.items())),
    )


def scan_return_use_or_failure(
    program: Any,
    entry_offset: int,
    register_names: Mapping[str, str],
    *,
    should_stop: Callable[[], bool] = lambda: False,
) -> ReturnUseEvidence:
    """``scan_return_use``, with a failure to read the program returned as a
    ``FAILED`` record (never raised: the consumer then does not use the evidence)."""
    import jpype  # noqa: PLC0415

    try:
        return scan_return_use(program, entry_offset, register_names, should_stop=should_stop)
    except (jpype.JException, ArithmeticError, AttributeError, LookupError, TypeError, ValueError) as error:
        return ReturnUseEvidence("FAILED", tuple(sorted(register_names.items())),
                                 detail=f"{type(error).__name__}: {error}"[:200])


__all__ = [
    "CallsiteDemand", "MAX_CALLSITES", "MAX_REGION_INSTRUCTIONS", "Op", "RETURN_USE_EVIDENCE_VERSION",
    "ReturnUseEvidence", "STACK_BASE_REGISTERS", "Vn", "demanded_bits", "fold_constants", "own_write",
    "prefix_bits", "producer_limit", "scan_return_use", "scan_return_use_or_failure",
]
