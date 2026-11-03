# -*- coding: utf-8 -*-
"""frame への access と、frame の外への access の alias・順序の証拠（Issue #282 AC 9、PR #289 review）。

入口の pointer・global の番地は呼び出し側が決めるので、entry SP より下（や stack で渡る引数の領域）を指し得る
（AC 9。「指さない」という一律の前提は置かない）。そのとき、関数の frame への access と、pointer・global 経由の
access は同じ cell に当たり得る:

* frame へ書いた後の pointer の読み出しは、frame の値を読み得る
* pointer へ書いた後の frame の読み出し（stack 変数の使用、退避した register の復元）は、その値を読み得る
* pointer へ書いた後の frame への書き込みは、観測する `*p` の最終値を変え得る

high P-code はこの関係を見せない: decompiler は frame の slot を SSA の値（stack 変数）にし、prologue の
退避・畳み込んだ spill・callee の frame への書き込みは op として残らない。そこで **機械語の P-code（命令ごとの
raw P-code）** を関数の body 全体で読み、各 memory access の番地が SP からだけ作られたか（frame: F）、SP を
含まないか（frame の外: N）、両方を含むか（U）を、命令の CFG の上の前向きの解析で分類する。

alias も順序も証明しない（frame の範囲・pointer の値は分からない）。代わりに、影響が起こり得る組み合わせが
**無い** ことの証拠だけを数える。次のどれかがあれば「証拠なし」:

* F と N の両方がある（順序によらず: 退避・spill は op の順に関係なく起こる）
* U がある（SP と他の値の両方から作った番地。frame の外にも届き得る）
* 呼び出し（`CALL` / `CALLIND` / `CALLOTHER`、body の外への分岐）がある（callee の frame への書き込みは
  entry SP より下へ届き、callee が何を読み書きするかもこの関数の命令からは分からない）
* 命令・P-code・CFG を読めない、行き先の分からない間接分岐がある、到達しない命令に access がある

frame だけを使う関数（O0 の spill だけの関数など）と、frame を使わない関数（frame を持たない leaf）は証拠ありに
なり、判定を変えない。証拠なしの関数は効果を不完全にし（`effect_store_location_unmodeled`: frame の store の
既存の理由と同じ）、EQ と NOT_EQ を止める。
"""

from __future__ import annotations

from typing import Dict, FrozenSet, Iterable, List, Optional, Set, Tuple

#: 番地の値の出自
_SP = "sp"
_OTHER = "other"

_FRAME = "frame"
_OUTSIDE = "outside"
_MIXED = "mixed"

_CALL_MNEMONICS = {"CALL", "CALLIND", "CALLOTHER"}
_BRANCH_MNEMONICS = {"BRANCH", "CBRANCH"}

#: 解析する命令数の上限（超えたら証拠なし）
_MAX_INSTRUCTIONS = 20000
#: fixpoint の反復の上限（命令あたり）。register ごとの taint は単調に増える（高さ 2）ので、register の数で抑えられる
_MAX_VISITS_PER_INSTRUCTION = 64


class _NoEvidence(Exception):
    pass


def _read_errors() -> Tuple[type, ...]:
    from scripts.function_tracer_pcode.analysis.program_points import ghidra_read_errors

    return ghidra_read_errors() + (LookupError,)


def _call(target, name: str, *args):
    method = getattr(target, name, None)
    if not callable(method):
        raise _NoEvidence(f"{name} is unavailable")
    try:
        return method(*args)
    except _read_errors() as exc:
        raise _NoEvidence(f"{name} failed: {type(exc).__name__}") from exc


def _items(value) -> list:
    if value is None:
        return []
    has_next = getattr(value, "hasNext", None)
    if callable(has_next):
        items = []
        while _bool(_call(value, "hasNext")):
            items.append(_call(value, "next"))
        return items
    try:
        return list(value)
    except TypeError as exc:
        raise _NoEvidence("not iterable") from exc


def _bool(value) -> bool:
    if isinstance(value, bool):
        return value
    text = str(value)
    if text in ("True", "true"):
        return True
    if text in ("False", "false"):
        return False
    raise _NoEvidence(f"not a boolean: {text!r}")


def _int(value) -> int:
    if isinstance(value, bool) or value is None:
        raise _NoEvidence("not an integer")
    try:
        return int(value)
    except (TypeError, ValueError) as exc:
        raise _NoEvidence("not an integer") from exc


def _address_offset(address) -> Optional[int]:
    if address is None:
        return None
    return _int(_call(address, "getOffset"))


def _space_name(varnode) -> str:
    address = _call(varnode, "getAddress")
    space = _call(address, "getAddressSpace")
    return str(_call(space, "getName"))


class _Instruction:
    __slots__ = ("address", "ops", "successors", "in_delay_slot")

    def __init__(self, address: int, ops: list, successors: List[int], in_delay_slot: bool) -> None:
        self.address = address
        self.ops = ops
        self.successors = successors
        self.in_delay_slot = in_delay_slot


def _stack_pointer_offset(program) -> int:
    spec = _call(program, "getCompilerSpec")
    register = _call(spec, "getStackPointer")
    if register is None:
        raise _NoEvidence("no stack pointer")
    return _address_offset(_call(register, "getAddress"))


def _load_instructions(program, function) -> Tuple[int, Dict[int, _Instruction]]:
    listing = _call(program, "getListing")
    body = _call(function, "getBody")
    entry = _address_offset(_call(function, "getEntryPoint"))
    instructions: Dict[int, _Instruction] = {}
    for instruction in _items(_call(listing, "getInstructions", body, True)):
        address = _address_offset(_call(instruction, "getAddress"))
        ops = _items(_call(instruction, "getPcode"))
        successors = []
        fall_through = _call(instruction, "getFallThrough")
        if fall_through is not None:
            successors.append(_address_offset(fall_through))
        for flow in _items(_call(instruction, "getFlows")):
            successors.append(_address_offset(flow))
        instructions[address] = _Instruction(
            address, ops, successors, _bool(_call(instruction, "isInDelaySlot"))
        )
        if len(instructions) > _MAX_INSTRUCTIONS:
            raise _NoEvidence("too many instructions")
    if entry not in instructions:
        raise _NoEvidence("entry instruction is not in the body")
    return entry, instructions


class _Scan:
    def __init__(self, sp_offset: int, instructions: Dict[int, _Instruction]) -> None:
        self.sp = sp_offset
        self.instructions = instructions
        self.accesses: Set[str] = set()

    def _register_taint(self, state: Dict[int, FrozenSet[str]], offset: int) -> FrozenSet[str]:
        if offset in state:
            return state[offset]
        # 入口の値: SP は SP、他の register は呼び出し側の値（frame の外の番地にもなり得る）
        return frozenset({_SP}) if offset == self.sp else frozenset({_OTHER})

    def _taint(self, varnode, state, uniques) -> FrozenSet[str]:
        if _bool(_call(varnode, "isConstant")):
            return frozenset()
        offset = _int(_call(varnode, "getOffset"))
        if _bool(_call(varnode, "isRegister")):
            return self._register_taint(state, offset)
        if _bool(_call(varnode, "isUnique")):
            return uniques.get(offset, frozenset({_OTHER}))
        # 命令が直接読む memory の operand（番地は定数）: frame の外への access
        self.accesses.add(_OUTSIDE)
        return frozenset({_OTHER})

    def _classify(self, taint: FrozenSet[str]) -> None:
        if _SP in taint and _OTHER in taint:
            self.accesses.add(_MIXED)
        elif _SP in taint:
            self.accesses.add(_FRAME)
        else:
            self.accesses.add(_OUTSIDE)

    def transfer(self, instruction: _Instruction, state: Dict[int, FrozenSet[str]]) -> Dict[int, FrozenSet[str]]:
        state = dict(state)
        uniques: Dict[int, FrozenSet[str]] = {}
        internal_branch = any(
            str(_call(op, "getMnemonic")) in _BRANCH_MNEMONICS
            and _bool(_call(_call(op, "getInput", 0), "isConstant"))
            for op in instruction.ops
        )
        for op in instruction.ops:
            mnemonic = str(_call(op, "getMnemonic"))
            inputs = [_call(op, "getInput", index) for index in range(_int(_call(op, "getNumInputs")))]
            if mnemonic in _CALL_MNEMONICS:
                raise _NoEvidence(f"call ({mnemonic})")
            if mnemonic == "BRANCHIND" and not instruction.successors:
                raise _NoEvidence("indirect branch without known targets")
            if mnemonic in _BRANCH_MNEMONICS and inputs and not _bool(_call(inputs[0], "isConstant")):
                target = _address_offset(_call(inputs[0], "getAddress"))
                if target not in self.instructions:
                    raise _NoEvidence("branch leaves the function body")
                continue
            if mnemonic == "STORE":
                self._classify(self._taint(inputs[1], state, uniques))
                self._taint(inputs[2], state, uniques)
                continue
            if mnemonic == "LOAD":
                self._classify(self._taint(inputs[1], state, uniques))
                taint = frozenset({_OTHER})
            else:
                taint = frozenset()
                for varnode in inputs:
                    taint = taint | self._taint(varnode, state, uniques)
            output = _call(op, "getOutput")
            if output is None:
                continue
            offset = _int(_call(output, "getOffset"))
            if _bool(_call(output, "isRegister")):
                if internal_branch:
                    taint = taint | self._register_taint(state, offset)
                state[offset] = taint
            elif _bool(_call(output, "isUnique")):
                uniques[offset] = taint | uniques.get(offset, frozenset()) if internal_branch else taint
            elif not _bool(_call(output, "isConstant")):
                self.accesses.add(_OUTSIDE)
        return state

    def run(self, entry: int) -> None:
        entry_state: Dict[int, FrozenSet[str]] = {}
        states: Dict[int, Dict[int, FrozenSet[str]]] = {entry: entry_state}
        visits: Dict[int, int] = {}
        worklist = [entry]
        while worklist:
            address = worklist.pop()
            visits[address] = visits.get(address, 0) + 1
            if visits[address] > _MAX_VISITS_PER_INSTRUCTION:
                raise _NoEvidence("fixpoint did not converge")
            instruction = self.instructions[address]
            out = self.transfer(instruction, states[address])
            for successor in instruction.successors:
                if successor not in self.instructions:
                    raise _NoEvidence("control leaves the function body")
                merged = _join(states.get(successor), out, self)
                if merged is not None:
                    states[successor] = merged
                    worklist.append(successor)
        for address, instruction in self.instructions.items():
            if address in states or instruction.in_delay_slot:
                continue
            # 到達しない命令（delay slot は分岐の P-code に含まれる）。access を持つなら分類できない
            for op in instruction.ops:
                if str(_call(op, "getMnemonic")) in {"LOAD", "STORE"} | _CALL_MNEMONICS:
                    raise _NoEvidence("unreached instruction accesses memory")


def _join(old, new, scan: _Scan):
    if old is None:
        return dict(new)
    keys = set(old) | set(new)
    merged = {
        key: scan._register_taint(old, key) | scan._register_taint(new, key)
        for key in keys
    }
    return None if merged == old else merged


def frame_alias_unproven(program, function) -> Optional[str]:
    """frame への access と frame の外への access の alias が判定に影響し得る（または証拠を作れない）なら、その
    理由の説明。影響し得る組み合わせが無いことを命令から示せたら None。"""

    try:
        sp_offset = _stack_pointer_offset(program)
        entry, instructions = _load_instructions(program, function)
        scan = _Scan(sp_offset, instructions)
        scan.run(entry)
    except _NoEvidence as exc:
        return str(exc)
    if _MIXED in scan.accesses:
        return "an address is built from both SP and another value"
    if _FRAME in scan.accesses and _OUTSIDE in scan.accesses:
        return "frame and non-frame memory accesses in one function"
    return None


def mark_frame_alias_unproven(summary) -> bool:
    """効果要約に frame の alias の理由（`effect_store_location_unmodeled`）を 1 度だけ足す（昇順・重複なし）。"""

    from scripts.function_tracer_pcode.analysis.effects._shared import _EFFECT_STORE_LOCATION_UNMODELED_REASON

    reasons = getattr(summary, "incomplete_reasons", ())
    if not isinstance(reasons, (list, tuple)):
        return False
    reasons = tuple(reasons)
    if _EFFECT_STORE_LOCATION_UNMODELED_REASON in reasons:
        return False
    summary.incomplete_reasons = tuple(sorted(set(reasons) | {_EFFECT_STORE_LOCATION_UNMODELED_REASON}))
    return True
