"""Issue #104 (PR 1): global / static memory writes are part of the observable
effect surface, never silently dropped.

Test matrix (Issue #104 PR 1):

  A. global direct STORE            -> StoreEffect on the symbol-named global
  B. RAM-space direct output (COPY) -> exit-copy post-state StoreEffect
  C. MULTIEQUAL merge of a global   -> branch-dependent effect, no silent drop
  D. stack-local store              -> excluded, no blocker
  E. pointer-argument store         -> unchanged behaviour
  F. global read only               -> no blocker
  G. call-induced INDIRECT on ram   -> not a direct write (Gap 3 / Gap 4 own it)
  H. effect-surface composition failure (Gap 5) -> never return-only comparison

The synthetic regressions here are unit fixtures, not EqBench ground truth.
"""
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.summary import (
    build_void_effect_summary_expr,
    canonicalize_location,
    canonicalize_param_location,
    classify_store_address,
    expression_reads_global_object,
    summarize_store_effects,
)
from scripts.function_tracer_pcode.analysis.effects._shared import (
    _EFFECT_GLOBAL_READ_IDENTITY_REASON,
    _EFFECT_STORE_LOCATION_UNMODELED_REASON,
    _EFFECT_SURFACE_COMPOSITION_REASON,
)
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.effect_integration import observable_store_effects
from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
    LoopSourceDisposition,
    classify_effect_incomplete_reasons,
)
from scripts.function_tracer_pcode.analysis.effects.observation_surface import (
    EFFECT_GLOBAL_STORE_IDENTITY_REASON as GLOBAL_STORE_REASON,
)
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    CanonicalLocation,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
    StorageInfo,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import forbid_callee_summary
from conftest import resolve_mock_data_type


# --------------------------------------------------------------------------
# Fixtures: Ghidra-shaped fakes for varnodes / ops / tracer
# --------------------------------------------------------------------------

def _global_ref(name, base, size, addr=None, *, program_id=1, writable=True, volatile=False):
    return AddressValueRef(
        address_offset=base if addr is None else addr,
        program_id=program_id,
        space_id=3,
        space_name="ram",
        symbol_name=name,
        block_name=".bss",
        is_initialized=False,
        can_read=True,
        can_write=writable,
        can_execute=False,
        is_volatile=volatile,
        object_symbol_name=name,
        object_base_offset=base,
        object_size=size,
    )


def _const_addr(ref, size=8):
    return Expression.constant(ref.address_offset, size, runtime_ref=ref)


def _global_read(ref, size):
    return Expression.memory(_const_addr(ref), size)


class _Address:
    def __init__(self, space, offset):
        self._space = space
        self._offset = offset

    def getAddressSpace(self):
        return self

    def getName(self):
        return self._space

    def getOffset(self):
        return self._offset

    def equals(self, other):
        return isinstance(other, _Address) and (self._space, self._offset) == (other._space, other._offset)


class _Varnode:
    def __init__(self, space, offset, size, *, defined_by=None, key=None):
        self._addr = _Address(space, offset)
        self._size = size
        self._def = defined_by
        self.key = key or f"{space}:{offset:#x}:{size}"

    def getAddress(self):
        return self._addr

    def getSize(self):
        return self._size

    def isAddress(self):
        return self._addr.getName() not in {"unique", "const", "register"}

    def getDef(self):
        return self._def


class _Seq:
    def __init__(self, target):
        self._target = target

    def getTarget(self):
        return self._target

    def getOrder(self):
        return 0


class _Op:
    __module__ = "ghidra.program.model.pcode"

    def __init__(self, mnemonic, output, inputs, target):
        self._mnemonic = mnemonic
        self._output = output
        self._inputs = list(inputs)
        self._seq = _Seq(target)

    def getMnemonic(self):
        return self._mnemonic

    def getOutput(self):
        return self._output

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getInputs(self):
        return list(self._inputs)

    def getSeqnum(self):
        return self._seq

    def getOpcode(self):
        return 0


class _Block:
    def __init__(self, ops, index=0):
        self.pcode_ops = list(ops)
        self.block = None
        self.index = index


class _Coverage:
    status = "complete"
    condition_paths = [[]]


class _Tracker:
    def get_path_coverage_to_block(self, _block):
        return _Coverage()


class _Tracer:
    """Tracer fake with a symbol table: ram offsets map to (name, base, size)."""

    def __init__(self, objects, values=None, readonly=()):
        self._objects = objects  # offset -> (name, base, size)
        self._values = values or {}
        self._readonly = set(readonly)

    def _ref_for_offset(self, offset):
        for name, base, size in self._objects:
            if base <= offset < base + size:
                return _global_ref(name, base, size, addr=offset)
        return None

    def ram_varnode_write_class(self, varnode):
        if varnode is None or not varnode.isAddress():
            return None
        if varnode.getAddress().getName() != "ram":
            return None
        offset = varnode.getAddress().getOffset()
        if offset in self._readonly:
            return "readonly"
        return "global" if self._ref_for_offset(offset) is not None else "unresolved"

    def global_object_location_for_varnode(self, varnode):
        if self.ram_varnode_write_class(varnode) != "global":
            return None
        ref = self._ref_for_offset(varnode.getAddress().getOffset())
        name, size, offset = ref.global_object_identity()
        return CanonicalLocation(
            base_ref=LocationBaseRef.global_object(name, size, space_name="ram"),
            offset=offset,
            size=varnode.getSize(),
        )

    def trace_varnode(self, varnode, use_cache=False, **_kwargs):
        if varnode.key in self._values:
            return self._values[varnode.key]
        if varnode.isAddress() and varnode.getAddress().getName() == "ram":
            ref = self._ref_for_offset(varnode.getAddress().getOffset())
            if ref is not None:
                return _global_read(ref, varnode.getSize())
        return Expression.unknown(varnode.key)


def _param(name, index, size=4, data_type="int"):
    return {"name": name, "index": index, "size": size, "data_type": data_type, "is_signed": True}


def _x():
    return Expression.parameter("param_1", 0, data_type="int", size=4)


G = ("g", 0x1000d0, 4)
H = ("h", 0x1000d8, 16)


# --------------------------------------------------------------------------
# Location model
# --------------------------------------------------------------------------

def test_global_location_identity_is_symbol_based_not_address_based():
    left = canonicalize_location(_const_addr(_global_ref("g", 0x1000d0, 4, program_id=1)), [], size=4)
    right = canonicalize_location(_const_addr(_global_ref("g", 0x2020a0, 4, program_id=2)), [], size=4)
    assert left is not None and right is not None
    assert left.base_ref.is_global()
    assert left == right
    assert left.base_ref.stable_key() == right.base_ref.stable_key()
    assert left.base_ref.global_symbol_name == "g"
    assert left.base_ref.to_dict()["kind"] == "global"


def test_global_location_keeps_the_offset_inside_the_object():
    location = canonicalize_location(_const_addr(_global_ref("h", 0x1000d8, 16, addr=0x1000dc)), [], size=4)
    assert location is not None
    assert location.base_ref.global_symbol_name == "h"
    assert location.offset == 4
    assert location.size == 4


@pytest.mark.parametrize(
    "ref",
    [
        AddressValueRef(address_offset=0x1000d0, can_write=True, is_volatile=False),  # no object symbol
        _global_ref("g", 0x1000d0, 4, writable=False),  # read-only data
        _global_ref("g", 0x1000d0, 4, volatile=True),  # volatile memory is never a plain object
        _global_ref("g", 0x1000d0, 4, addr=0x1000d8),  # outside the object
    ],
)
def test_constant_addresses_without_global_identity_do_not_canonicalize(ref):
    assert ref.global_object_identity() is None
    assert canonicalize_location(_const_addr(ref), [], size=4) is None


def test_bare_constant_address_is_not_a_location():
    assert canonicalize_location(Expression.constant(0x1000d0, 8), [], size=4) is None
    assert canonicalize_param_location(_const_addr(_global_ref(*G)), [], size=4) is None


def test_global_base_requires_the_global_object_identity_key():
    with pytest.raises(ValueError):
        LocationBaseRef(kind="global")
    with pytest.raises(ValueError):
        LocationBaseRef.global_object("", 4)


# --------------------------------------------------------------------------
# classify_store_address
# --------------------------------------------------------------------------

def _ptr_intrinsic(name, *operands):
    """PTRADD / PTRSUB as the tracer emits them: INTRINSIC nodes named by mnemonic."""
    from scripts.function_tracer_pcode.core import ExpressionType

    expr = Expression(ExpressionType.INTRINSIC, name=name, operands=list(operands), size=8)
    return expr


def _stack_pointer():
    return Expression.variable(
        "sp",
        size=8,
        storage_info=StorageInfo(is_register=True, space_name="register", register_name="sp", is_stack_pointer=True),
    )


def test_classify_store_address_distinguishes_parameter_global_stack_and_unresolved():
    params = [_param("param_1", 0, size=8, data_type="int *")]
    pointer = Expression.parameter("param_1", 0, data_type="int *", size=8)
    assert classify_store_address(pointer, params, size=4)[0] == "parameter"
    assert classify_store_address(_const_addr(_global_ref(*G)), params, size=4)[0] == "global"
    symbolic_index = _ptr_intrinsic(
        "PTRADD",
        _ptr_intrinsic("PTRSUB", _stack_pointer(), Expression.constant(-224, 8)),
        Expression.unknown("idx"),
        Expression.constant(8, 8),
    )
    # Issue #282 (I11): index を含む frame の番地は範囲を示せないので観測から外さない
    assert classify_store_address(symbolic_index, params, size=8) == ("unresolved", None)
    assert classify_store_address(Expression.constant(0x1000d0, 8), params, size=4) == ("unresolved", None)
    assert classify_store_address(Expression.unknown("escaped"), params, size=4) == ("unresolved", None)


# --------------------------------------------------------------------------
# A. global direct STORE
# --------------------------------------------------------------------------

def _store_op(addr_key, value_key, size, target=0x100):
    return _Op(
        "STORE",
        None,
        [_Varnode("const", 0x1b1, 4), _Varnode("unique", 0x10, 8, key=addr_key), _Varnode("register", 0x20, size, key=value_key)],
        _Address("ram", target),
    )


def test_global_direct_store_becomes_a_global_store_effect():
    tracer = _Tracer([G], values={"addr": _const_addr(_global_ref(*G)), "val": _x()})
    summary = summarize_store_effects([_Block([_store_op("addr", "val", 4)])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)

    assert summary.incomplete_reasons == (GLOBAL_STORE_REASON,)  # Issue #282: global の object の identity の証拠が無い
    assert summary.has_unsupported_call is False
    assert len(summary.effects) == 1
    effect = summary.effects[0]
    assert effect.location.base_ref.is_global()
    assert effect.location.base_ref.global_symbol_name == "g"
    assert effect.value.to_string() == "param_1"
    assert effect.provenance is not None and effect.provenance.source_kind == "local_store"
    assert observable_store_effects(summary) == summary.effects
    # Issue #282: global への store は比較面に入らない
    assert summary.synthetic_expr is None


def test_store_to_an_unresolved_address_fails_closed_instead_of_vanishing():
    """Old behaviour (soundness hole): the store was silently skipped and the
    function compared as if it had no effects.  New behaviour: fail closed."""
    tracer = _Tracer([G], values={"addr": Expression.constant(0x1000d0, 8), "val": _x()})
    summary = summarize_store_effects([_Block([_store_op("addr", "val", 4)])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)

    assert summary.effects == []
    assert summary.incomplete_reasons == (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)


def test_store_through_an_escaped_pointer_fails_closed():
    tracer = _Tracer([G], values={"addr": Expression.unknown("escaped_ptr"), "val": _x()})
    summary = summarize_store_effects([_Block([_store_op("addr", "val", 4)])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert summary.incomplete_reasons == (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)


# --------------------------------------------------------------------------
# D. stack local / E. pointer argument / F. read only
# --------------------------------------------------------------------------

def test_stack_local_store_with_symbolic_index_fails_closed():
    """Issue #282 (I11): `sp + index` は index が範囲外なら caller の領域に届く。範囲を示せないので外さない。"""

    addr = _ptr_intrinsic(
        "PTRADD",
        _ptr_intrinsic("PTRSUB", _stack_pointer(), Expression.constant(-224, 8)),
        Expression.unknown("idx"),
        Expression.constant(8, 8),
    )
    tracer = _Tracer([G], values={"addr": addr, "val": _x()})
    summary = summarize_store_effects([_Block([_store_op("addr", "val", 8)])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert summary.incomplete_reasons == (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)


def test_pointer_argument_store_is_unchanged_next_to_a_global_store():
    params = [_param("param_1", 0, size=8, data_type="int *"), _param("param_2", 1)]
    pointer = Expression.parameter("param_1", 0, data_type="int *", size=8)
    value = Expression.parameter("param_2", 1, data_type="int", size=4)
    tracer = _Tracer([G], values={"p": pointer, "gaddr": _const_addr(_global_ref(*G)), "val": value})
    ops = [_store_op("p", "val", 4, target=0x100), _store_op("gaddr", "val", 4, target=0x104)]
    summary = summarize_store_effects([_Block(ops)], tracer, _Tracker(), params, direct_call_summary=forbid_callee_summary)

    assert summary.incomplete_reasons == (GLOBAL_STORE_REASON,)  # Issue #282: global の object の identity の証拠が無い
    kinds = sorted(effect.location.base_ref.kind for effect in summary.effects)
    assert kinds == ["global", "parameter"]
    parameter_effect = next(effect for effect in summary.effects if effect.location.base_ref.is_parameter())
    assert parameter_effect.location.base_ref.parameter_index == 0
    assert parameter_effect.value.to_string() == "param_2"


def test_global_read_only_function_has_no_effects_and_no_blocker():
    g = _global_ref(*G)
    load = _Op("LOAD", _Varnode("unique", 0x30, 4, key="loaded"), [_Varnode("const", 0x1b1, 4), _Varnode("unique", 0x10, 8, key="addr")], _Address("ram", 0x100))
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8), _Varnode("register", 0x4000, 4)], _Address("ram", 0x108))
    tracer = _Tracer([G], values={"addr": _const_addr(g), "loaded": _global_read(g, 4)})
    summary = summarize_store_effects([_Block([load, ret])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert summary.incomplete_reasons == ()
    assert summary.has_unsupported_call is False
    assert expression_reads_global_object(_global_read(g, 4)) is True
    assert expression_reads_global_object(Expression.memory(Expression.constant(0x1000d0, 8), 4)) is False


def test_readonly_ram_outputs_are_ignored():
    """GOT / .rodata slots are read-only memory: not an observable write."""
    got = _Varnode("ram", 0x101000, 8)
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x108))
    exit_copy = _Op("COPY", got, [_Varnode("ram", 0x101000, 8, defined_by=object())], _Address("ram", 0x108))
    tracer = _Tracer([G], readonly={0x101000})
    summary = summarize_store_effects([_Block([exit_copy, ret])], tracer, _Tracker(), [], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert summary.incomplete_reasons == ()


# --------------------------------------------------------------------------
# B. RAM direct output / exit copies
# --------------------------------------------------------------------------

def _exit_copy(space_offset, size, defined, target):
    out = _Varnode("ram", space_offset, size)
    src = _Varnode("ram", space_offset, size, defined_by=object() if defined else None, key=f"exit:{space_offset:#x}")
    return _Op("COPY", out, [src], _Address("ram", target))


def test_ram_output_copy_is_observed_through_the_return_site_exit_copy():
    """ARM64 gcc -O0 shape: ``g = x`` is ``COPY (ram,g) <- register`` and the
    return site carries ``COPY (ram,g) <- (ram,g')``; no STORE op exists."""
    write = _Op("COPY", _Varnode("ram", 0x1000d0, 4), [_Varnode("register", 0x4000, 4, key="x")], _Address("ram", 0x14))
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8), _Varnode("register", 0x4000, 8)], _Address("ram", 0x20))
    exit_copy = _exit_copy(0x1000d0, 4, True, 0x20)
    tracer = _Tracer([G], values={"x": _x(), "exit:0x1000d0": _x()})
    summary = summarize_store_effects([_Block([write, ret, exit_copy])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)

    assert summary.incomplete_reasons == (GLOBAL_STORE_REASON,)  # Issue #282: global の object の identity の証拠が無い
    assert len(summary.effects) == 1
    effect = summary.effects[0]
    assert effect.location.base_ref.global_symbol_name == "g"
    assert effect.location.size == 4
    assert effect.value.to_string() == "param_1"
    assert effect.provenance.source_kind == "local_store"


def test_unchanged_global_exit_copy_produces_no_effect():
    """A global that is only read keeps its entry value at the return site."""
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x20))
    exit_copy = _exit_copy(0x1000d0, 4, False, 0x20)
    summary = summarize_store_effects([_Block([ret, exit_copy])], _Tracer([G]), _Tracker(), [], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert summary.incomplete_reasons == ()


def test_ram_output_write_without_exit_copy_fails_closed():
    write = _Op("COPY", _Varnode("ram", 0x1000d0, 4), [_Varnode("register", 0x4000, 4, key="x")], _Address("ram", 0x14))
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x20))
    tracer = _Tracer([G], values={"x": _x()})
    summary = summarize_store_effects([_Block([write, ret])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert _EFFECT_STORE_LOCATION_UNMODELED_REASON in summary.incomplete_reasons


def test_ram_output_write_to_an_unnamed_object_fails_closed():
    write = _Op("COPY", _Varnode("ram", 0x2000, 4), [_Varnode("register", 0x4000, 4, key="x")], _Address("ram", 0x14))
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x20))
    exit_copy = _exit_copy(0x2000, 4, True, 0x20)
    tracer = _Tracer([G], values={"x": _x(), "exit:0x2000": _x()})
    summary = summarize_store_effects([_Block([write, ret, exit_copy])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert summary.effects == []
    assert _EFFECT_STORE_LOCATION_UNMODELED_REASON in summary.incomplete_reasons


def test_exit_copies_at_every_return_site_each_contribute_the_path_value():
    ret1 = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x20))
    ret2 = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x40))
    exit1 = _exit_copy(0x1000d0, 4, True, 0x20)
    exit2 = _exit_copy(0x1000d0, 4, False, 0x40)
    write = _Op("COPY", _Varnode("ram", 0x1000d0, 4), [_Varnode("register", 0x4000, 4, key="x")], _Address("ram", 0x14))
    tracer = _Tracer([G], values={"x": _x(), "exit:0x1000d0": _x()})
    summary = summarize_store_effects(
        [_Block([write, ret1, exit1], 0), _Block([ret2, exit2], 1)], tracer, _Tracker(), [_param("param_1", 0)],
        direct_call_summary=forbid_callee_summary
    )
    assert summary.incomplete_reasons == (GLOBAL_STORE_REASON,)  # Issue #282: global の object の identity の証拠が無い
    assert len(summary.effects) == 1


# --------------------------------------------------------------------------
# C. MULTIEQUAL merge
# --------------------------------------------------------------------------

def test_multiequal_merged_global_is_observed_as_a_branch_dependent_value():
    phi = Expression.phi([(None, _x()), (None, Expression.unary_op("INT_NEGATE", _x()))])
    merge = _Op("MULTIEQUAL", _Varnode("ram", 0x1000d0, 4), [_Varnode("unique", 0x1, 4), _Varnode("unique", 0x2, 4)], _Address("ram", 0x60))
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x68))
    exit_copy = _exit_copy(0x1000d0, 4, True, 0x68)
    tracer = _Tracer([G], values={"exit:0x1000d0": phi})
    summary = summarize_store_effects([_Block([merge, ret, exit_copy])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert summary.incomplete_reasons == (GLOBAL_STORE_REASON,)  # Issue #282: global の object の identity の証拠が無い
    assert len(summary.effects) == 1
    assert summary.effects[0].value is phi


# --------------------------------------------------------------------------
# G. call-induced INDIRECT
# --------------------------------------------------------------------------

def test_call_induced_indirect_on_ram_is_not_a_direct_write():
    """``INDIRECT (ram,g) <- (ram,g), call`` marks a possible callee effect; it
    is owned by the call-effect lane (Gap 3 / Gap 4), never modelled here."""
    call = _Op("CALL", _Varnode("register", 0x4000, 8), [_Varnode("ram", 0x101000, 8)], _Address("ram", 0x30))
    indirect = _Op("INDIRECT", _Varnode("ram", 0x1000d0, 4), [_Varnode("ram", 0x1000d0, 4), _Varnode("const", 0x30, 4)], _Address("ram", 0x30))
    ret = _Op("RETURN", None, [_Varnode("const", 0, 8)], _Address("ram", 0x40))
    exit_copy = _exit_copy(0x1000d0, 4, False, 0x40)
    summary = summarize_store_effects([_Block([call, indirect, ret, exit_copy])], _Tracer([G]), _Tracker(), [], direct_call_summary=lambda _target_ref, _arguments: None)
    assert summary.effects == []
    assert _EFFECT_STORE_LOCATION_UNMODELED_REASON not in summary.incomplete_reasons
    # Issue #121: callee summary が無い call は call-effect lane の blocker として
    # 記録される（読み飛ばされない）。この test の前提を明示する。
    assert summary.has_unsupported_call is True
    assert {ref.reason for ref in summary.unsupported_call_sites} == {"target_identity_unavailable"}


# --------------------------------------------------------------------------
# Global reads inside modelled effects
# --------------------------------------------------------------------------

def test_global_effect_value_reading_a_named_global_is_modelled():
    """Reads of named globals render against a shared symbolic base address,
    so ``g = h + x`` is a complete effect."""
    g = _global_ref(*G)
    h = _global_ref(*H)
    value = Expression.binary_op("INT_ADD", _global_read(h, 4), _x())
    tracer = _Tracer([G, H], values={"addr": _const_addr(g), "val": value})
    summary = summarize_store_effects([_Block([_store_op("addr", "val", 4)])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert len(summary.effects) == 1
    assert summary.incomplete_reasons == (GLOBAL_STORE_REASON,)  # Issue #282: global の object の identity の証拠が無い


def _unidentified_writable_ref(addr):
    return AddressValueRef(address_offset=addr, program_id=1, space_id=3, space_name="ram", block_name=".bss",
                           is_initialized=False, can_read=True, can_write=True, can_execute=False, is_volatile=False)


def test_global_effect_value_reading_unidentified_writable_memory_fails_closed():
    """A writable address without a symbol (stripped binary) is keyed by its
    absolute address only and cannot unify across binaries."""
    g = _global_ref(*G)
    value = Expression.binary_op("INT_ADD", Expression.memory(_const_addr(_unidentified_writable_ref(0x2000)), 4), _x())
    tracer = _Tracer([G], values={"addr": _const_addr(g), "val": value})
    summary = summarize_store_effects([_Block([_store_op("addr", "val", 4)])], tracer, _Tracker(), [_param("param_1", 0)], direct_call_summary=forbid_callee_summary)
    assert len(summary.effects) == 1
    assert _EFFECT_GLOBAL_READ_IDENTITY_REASON in summary.incomplete_reasons


# --------------------------------------------------------------------------
# Non-void synthetic pair: int f(int x){ g = x; return 0; } vs int f(int x){ return 0; }
# --------------------------------------------------------------------------

def _analyzer():
    analyzer = ReturnAnalyzer(Mock(), debug=False)
    analyzer._parameters.is_void_type = lambda dtype: str(dtype) == "void"
    return analyzer


def _int_function(effects):
    analysis = FunctionReturnAnalysis(
        function_name="f", entry_point="0x1000",
        parameters=[_param("param_1", 0)],
        returns=[ReturnInfo("0x1010", Expression.constant(0, size=4), [])],
        return_type="int",
        return_type_obj=resolve_mock_data_type("int"),
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1"], effects=list(effects))
    analysis.effect_summary.synthetic_expr = build_void_effect_summary_expr(list(effects))
    return analysis


def _global_effect(name, base, size, value, order=1):
    location = CanonicalLocation(base_ref=LocationBaseRef.global_object(name, size, space_name="ram"), offset=0, size=size)
    return StoreEffect(location=location, value=value, conditions=[], order_key=order)


def test_non_void_global_store_blocks_the_comparison_without_identity_evidence():
    """Issue #282 (I1): 左右の global の object が同じである根拠が無いので、global への store は比較面に入らず、
    効果を不完全にする（戻り値だけで比べることもしない）。"""
    analyzer = _analyzer()
    with_store = _int_function([_global_effect("g", 0x1000d0, 4, _x())])
    without_store = _int_function([])

    assert analyzer._apply_observable_effect_surface(with_store, with_store.return_type_obj, "int") is False
    assert with_store.comparison_surface is None
    assert GLOBAL_STORE_REASON in with_store.effect_summary.incomplete_reasons
    assert GLOBAL_STORE_REASON in with_store.get_equivalence_blocking_unsafety_reasons()
    assert GLOBAL_STORE_REASON in with_store.get_decisive_sat_unsafety_reasons()

    assert analyzer._apply_observable_effect_surface(without_store, without_store.return_type_obj, "int") is False
    assert without_store.comparison_surface is None
    assert without_store.effect_summary.incomplete_reasons == ()


def test_two_binaries_with_the_same_global_store_are_not_identified_by_the_symbol_name():
    """Issue #282 (I1): 名前と大きさが同じ global でも、同じ object である根拠（identity の証拠）が無い。
    以前は symbol の名前から作った共有の記号で同じ面にしていた。"""
    analyzer = _analyzer()
    left = _int_function([_global_effect("g", 0x1000d0, 4, _x())])
    right = _int_function([_global_effect("g", 0x2020a0, 4, _x())])
    for analysis in (left, right):
        assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, "int") is False
        assert analysis.comparison_surface is None
        assert GLOBAL_STORE_REASON in analysis.effect_summary.incomplete_reasons


# --------------------------------------------------------------------------
# H. Gap 5: effect-surface composition failure
# --------------------------------------------------------------------------

def _sret_like(return_values):
    obj = Expression.parameter("param_1", 0, data_type="undefined8 *", size=8)
    r = Expression.parameter("param_2", 1, data_type="int", size=4)
    effects = [StoreEffect(location=CanonicalLocation(base_param="param_1", offset=0, size=4), value=r, conditions=[], order_key=1)]
    analysis = FunctionReturnAnalysis(
        function_name="ctor", entry_point="0x1000",
        parameters=[_param("param_1", 0, size=8, data_type="undefined8 *"), _param("param_2", 1)],
        returns=[ReturnInfo(f"0x10{index}0", value, []) for index, value in enumerate(return_values)],
        return_type="undefined8 *",
        return_type_obj=resolve_mock_data_type("undefined8 *"),
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1", "param_2"], effects=effects)
    analysis.effect_summary.synthetic_expr = build_void_effect_summary_expr(effects)
    return analysis, obj


def test_return_width_mismatch_with_stores_is_a_registered_blocker_not_a_return_only_fallback():
    """Old behaviour (soundness hole): the stores were dropped and the pair was
    compared on the return value only.  New behaviour: fail closed."""
    analyzer = _analyzer()
    analysis, obj = _sret_like([obj_value for obj_value in (Expression.parameter("param_1", 0, data_type="undefined8 *", size=8), Expression.constant(0, size=1))])
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, analysis.return_type) is False
    assert analysis.comparison_surface is None
    assert analysis.effect_summary.incomplete_reasons == (_EFFECT_SURFACE_COMPOSITION_REASON,)
    assert _EFFECT_SURFACE_COMPOSITION_REASON in analysis.get_equivalence_blocking_unsafety_reasons()
    assert _EFFECT_SURFACE_COMPOSITION_REASON in analysis.get_decisive_sat_unsafety_reasons()


def test_stores_without_any_return_observation_are_a_registered_blocker():
    analyzer = _analyzer()
    analysis, _obj = _sret_like([])
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, analysis.return_type) is False
    assert analysis.effect_summary.incomplete_reasons == (_EFFECT_SURFACE_COMPOSITION_REASON,)


def test_existing_blockers_are_not_duplicated_by_the_composition_check():
    analyzer = _analyzer()
    analysis, _obj = _sret_like([Expression.parameter("param_1", 0, data_type="undefined8 *", size=8), Expression.constant(0, size=1)])
    analysis.effect_summary.incomplete_reasons = ("effect_summary_path_coverage_incomplete",)
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, analysis.return_type) is False
    assert analysis.effect_summary.incomplete_reasons == ("effect_summary_path_coverage_incomplete",)

    unsupported, _obj = _sret_like([Expression.parameter("param_1", 0, data_type="undefined8 *", size=8), Expression.constant(0, size=1)])
    unsupported.effect_summary.has_unsupported_call = True
    assert analyzer._apply_observable_effect_surface(unsupported, unsupported.return_type_obj, unsupported.return_type) is False
    assert unsupported.effect_summary.incomplete_reasons == ()


def test_global_effect_next_to_a_named_global_read_in_the_return_is_composed():
    analyzer = _analyzer()
    analysis = _int_function([_global_effect("h", 0x1000d8, 16, _x())])
    analysis.returns = [ReturnInfo("0x1010", _global_read(_global_ref(*G), 4), [])]
    # Issue #282 (I1): global への store は比較面に入らない（identity の証拠が無い）
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, "int") is False
    assert analysis.effect_summary.incomplete_reasons == (GLOBAL_STORE_REASON,)


def test_global_effect_next_to_an_unidentified_writable_read_in_the_return_fails_closed():
    analyzer = _analyzer()
    analysis = _int_function([_global_effect("h", 0x1000d8, 16, _x())])
    analysis.returns = [ReturnInfo("0x1010", Expression.memory(_const_addr(_unidentified_writable_ref(0x2000)), 4), [])]
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, "int") is False
    assert analysis.effect_summary.incomplete_reasons == (_EFFECT_GLOBAL_READ_IDENTITY_REASON,)


def test_void_surface_is_not_built_from_an_incomplete_effect_summary():
    from scripts.function_tracer_pcode.analysis.returns.analyze_function import (
        _effect_summary_incomplete_reasons,
    )

    summary = EffectSummary(parameter_names=[], effects=[])
    summary.incomplete_reasons = (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)
    assert _effect_summary_incomplete_reasons(summary) == (_EFFECT_STORE_LOCATION_UNMODELED_REASON,)
    assert _effect_summary_incomplete_reasons(Mock()) == ()


# --------------------------------------------------------------------------
# Reason token ownership
# --------------------------------------------------------------------------

@pytest.mark.parametrize(
    "token",
    [
        _EFFECT_STORE_LOCATION_UNMODELED_REASON,
        _EFFECT_GLOBAL_READ_IDENTITY_REASON,
        _EFFECT_SURFACE_COMPOSITION_REASON,
    ],
)
def test_new_effect_tokens_are_owned_by_the_effect_observation_coverage_reason(token):
    classified = classify_effect_incomplete_reasons((token,))
    assert classified.disposition is LoopSourceDisposition.REFINED_TO_SLICE3
    assert classified.reason_ids == ("effect_observation_coverage_incomplete",)
    strategy = PairwiseStrategy.__new__(PairwiseStrategy)
    assert strategy._unknown_reason_id_for_blocking_unsafety(token) == "effect_observation_coverage_incomplete"


# --------------------------------------------------------------------------
# MIPS64 shapes: constant address behind INDIRECT / PHI (GOT reload after a store)
# --------------------------------------------------------------------------

def test_indirect_of_a_global_address_constant_canonicalizes_to_the_global():
    g = _global_ref(*G)
    indirect = Expression.binary_op("INDIRECT", _const_addr(g), Expression.constant(271, 4))
    location = canonicalize_location(indirect, [], size=4)
    assert location is not None and location.base_ref.global_symbol_name == "g"
    nested = Expression.binary_op("INDIRECT", indirect, Expression.constant(286, 4))
    assert canonicalize_location(nested, [], size=4) == location
    bare = Expression.binary_op("INDIRECT", Expression.constant(0x1000d0, 8), Expression.constant(271, 4))
    assert canonicalize_location(bare, [], size=4) is None
    assert expression_reads_global_object(Expression.memory(indirect, 4)) is True


def test_phi_of_the_same_global_address_canonicalizes_but_mixed_targets_do_not():
    g = _global_ref(*G)
    h = _global_ref(*H)
    same = Expression.phi([(None, _const_addr(g)), (None, Expression.binary_op("INDIRECT", _const_addr(g), Expression.constant(1, 4)))])
    location = canonicalize_location(same, [], size=4)
    assert location is not None and location.base_ref.global_symbol_name == "g"
    mixed = Expression.phi([(None, _const_addr(g)), (None, _const_addr(h))])
    assert canonicalize_location(mixed, [], size=4) is None
    assert classify_store_address(mixed, [], size=4) == ("unresolved", None)
