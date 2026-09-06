"""Issue #104 follow-up: reads and writes of a named writable global are keyed
by the symbol, not by the absolute address of one binary.

The SMT formula gives every named global object a *shared* symbolic base
address (``gaddr_<symbol>``), declared once for both sides and constrained to
be non-null, non-wrapping and disjoint from the other objects.  Loads keep
their array-select semantics (``(select memN (bvadd gaddr off))``), so a
parameter pointer may still alias a global exactly as before; only the
cross-binary identity changes.  Unit fixtures here are synthetic, not EqBench
ground truth.
"""
import shutil
import subprocess

import pytest

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.summary import build_void_effect_summary_expr
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    CanonicalLocation,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.render_smt import (
    collect_global_address_identities,
    collect_unknown_smt_declarations,
    global_address_symbol_name,
)
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    counterexample_replay_targets,
)
from scripts.function_tracer_pcode.semantics.semantic_width import normalize_analysis_semantic_width
from scripts.function_tracer_pcode.tests.unit.test_global_effect_surface_issue104 import (
    _const_addr,
    _global_read,
    _global_ref,
    _param,
)
from unittest.mock import Mock
from conftest import resolve_mock_data_type


def _run_z3(query: str) -> str:
    z3_path = shutil.which("z3")
    if z3_path is None:
        pytest.skip("z3 is not available in PATH")
    completed = subprocess.run([z3_path, "-in"], input=query.replace("(get-model)", ""), text=True, capture_output=True, check=False)
    assert completed.returncode == 0, completed.stderr
    assert completed.stderr == ""
    return completed.stdout.strip().splitlines()[0]


# --------------------------------------------------------------------------
# rendering
# --------------------------------------------------------------------------

def test_global_address_constant_renders_as_the_shared_base_symbol():
    left = _const_addr(_global_ref("g", 0x1000d0, 4, program_id=1))
    right = _const_addr(_global_ref("g", 0x2020a0, 4, program_id=2))
    symbol = global_address_symbol_name(("g", 4, 0))
    assert left.to_smt() == symbol
    assert right.to_smt() == symbol
    inner = _const_addr(_global_ref("h", 0x1000d8, 16, addr=0x1000dc))
    assert inner.to_smt() == f"(bvadd {global_address_symbol_name(('h', 16, 0))} (_ bv4 64))"
    # a 32-bit constant carrying an identity keeps its width
    narrow = Expression.constant(0x1000d0, 4, runtime_ref=_global_ref("g", 0x1000d0, 4))
    assert narrow.to_smt() == f"((_ extract 31 0) {symbol})"


def test_global_reads_on_two_binaries_select_the_same_shared_cell():
    left = _global_read(_global_ref("g", 0x1000d0, 4, program_id=1), 4)
    right = _global_read(_global_ref("g", 0x2020a0, 4, program_id=2), 4)
    assert left.to_smt() == right.to_smt()
    assert left.to_smt() == f"(select mem32 {global_address_symbol_name(('g', 4, 0))})"


def test_constants_without_identity_still_render_literally():
    assert Expression.constant(0x1000d0, 8).to_smt() == "(_ bv1048784 64)"
    readonly = AddressValueRef(address_offset=0x3000, can_write=False, is_volatile=False, object_symbol_name="tbl", object_base_offset=0x3000, object_size=8)
    assert Expression.constant(0x3000, 8, runtime_ref=readonly).to_smt() == "(_ bv12288 64)"


def test_global_base_symbols_are_declared_with_the_runtime_unknowns_and_collected():
    g = _global_ref("g", 0x1000d0, 4)
    h = _global_ref("h", 0x1000d8, 16, addr=0x1000dc)
    expr = Expression.binary_op("INT_ADD", _global_read(g, 4), Expression.memory(_const_addr(h), 4))
    declarations = collect_unknown_smt_declarations(expr)
    assert (global_address_symbol_name(("g", 4, 0)), 64) in declarations
    assert (global_address_symbol_name(("h", 16, 0)), 64) in declarations
    assert collect_global_address_identities(expr) == [("g", 4), ("h", 16)]


def test_symbol_names_are_sanitised_and_size_qualified():
    a = global_address_symbol_name(("my.var", 4, 0))
    b = global_address_symbol_name(("my_var", 4, 0))
    c = global_address_symbol_name(("my_var", 8, 0))
    assert a.startswith("gaddr_my_var_4_") and b.startswith("gaddr_my_var_4_")
    assert a != b and b != c


# --------------------------------------------------------------------------
# formula builder + solver
# --------------------------------------------------------------------------

def _analyzer():
    analyzer = ReturnAnalyzer(Mock(), debug=False)
    analyzer._parameters.is_void_type = lambda dtype: str(dtype) == "void"
    return analyzer


def _x():
    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _global_function(name, base, op, *, program_id):
    """``int f(int x) { g = g <op> x; return 0; }`` with ``g`` at ``base``."""
    ref = _global_ref(name, base, 4, program_id=program_id)
    value = Expression.binary_op(op, _global_read(ref, 4), _x())
    location = CanonicalLocation(base_ref=LocationBaseRef.global_object(name, 4, space_name="ram"), offset=0, size=4)
    effects = [StoreEffect(location=location, value=value, conditions=[], order_key=1)]
    analysis = FunctionReturnAnalysis(
        function_name="f", entry_point="0x1000", parameters=[_param("param_1", 0)],
        returns=[ReturnInfo("0x1010", Expression.constant(0, size=4), [])],
        return_type="int", return_type_obj=resolve_mock_data_type("int"),
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1"], effects=effects)
    analysis.effect_summary.synthetic_expr = build_void_effect_summary_expr(effects)
    analyzer = _analyzer()
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, "int") is True
    return analysis


def _pair_query(left, right):
    left = normalize_analysis_semantic_width(left)
    right = normalize_analysis_semantic_width(right)
    builder = FormulaBuilder(debug=False, exclude_ub=False)
    base_ctx = builder.build_base_context(left, right)
    cases1 = extract_return_cases(left)
    cases2 = extract_return_cases(right)
    replace1 = build_symbol_replacer(base_ctx["params1"], base_ctx.get("extra_vars1", []))
    replace2 = build_symbol_replacer(base_ctx["params2"], base_ctx.get("extra_vars2", []))
    return base_ctx, build_pair_query(base_ctx, cases1[0], cases2[0], replace1, replace2, "(0,0)")


def test_same_global_update_on_two_binaries_is_provably_equal():
    """``g = g + x`` at 0x1000d0 (binary 1) vs at 0x2020a0 (binary 2): UNSAT."""
    left = _global_function("g", 0x1000d0, "INT_ADD", program_id=1)
    right = _global_function("g", 0x2020a0, "INT_ADD", program_id=2)
    base_ctx, query = _pair_query(left, right)
    symbol = global_address_symbol_name(("g", 4, 0))
    assert query.count(f"(declare-const {symbol} (_ BitVec 64))") == 1
    assert f"(assert (not (= {symbol} (_ bv0 64))))" in query
    assert "1048784" not in query and "2105504" not in query  # no absolute addresses
    assert (symbol, 64) in counterexample_replay_targets(base_ctx)
    assert _run_z3(query) == "unsat"


def test_different_global_updates_are_not_equal():
    """``g = g + x`` vs ``g = g - x``: SAT (a real observable difference)."""
    left = _global_function("g", 0x1000d0, "INT_ADD", program_id=1)
    right = _global_function("g", 0x2020a0, "INT_SUB", program_id=2)
    _base_ctx, query = _pair_query(left, right)
    assert _run_z3(query) == "sat"


def test_distinct_globals_are_disjoint_in_the_formula():
    left = _global_function("g", 0x1000d0, "INT_ADD", program_id=1)
    right = _global_function("h", 0x2020a0, "INT_ADD", program_id=2)
    _base_ctx, query = _pair_query(left, right)
    g = global_address_symbol_name(("g", 4, 0))
    h = global_address_symbol_name(("h", 4, 0))
    assert f"(assert (or (bvule (bvadd {g} (_ bv4 64)) {h}) (bvule (bvadd {h} (_ bv4 64)) {g})))" in query
    # writing g vs writing h: different surfaces, never equal
    assert _run_z3(query) == "sat"


# --------------------------------------------------------------------------
# ram_varnode_write_class hardening: address-space attribute
# --------------------------------------------------------------------------

def test_ram_varnode_write_class_requires_a_real_memory_address_space():
    from scripts.function_tracer_pcode.analysis.tracer_addresses import AddressRefMixin

    class _Space:
        def __init__(self, name, memory):
            self._name, self._memory = name, memory

        def getName(self):
            return self._name

        def isMemorySpace(self):
            return self._memory

    class _Addr:
        def __init__(self, space):
            self._space = space

        def getAddressSpace(self):
            return self._space

        def getOffset(self):
            return 0x1000d0

    class _Varnode:
        def __init__(self, space):
            self._addr = _Addr(space)

        def isAddress(self):
            return True

        def getAddress(self):
            return self._addr

        def getSize(self):
            return 4

    class _Tracer(AddressRefMixin):
        program = None
        debug = False
        calls = []

        def _make_address_runtime_ref_for_offset(self, offset, **kwargs):
            self.calls.append(offset)
            return _global_ref("g", 0x1000d0, 4)

    tracer = _Tracer()
    assert tracer.ram_varnode_write_class(_Varnode(_Space("ram", True))) == "global"
    assert tracer.ram_varnode_write_class(_Varnode(_Space("OTHER", False))) is None
    assert tracer.ram_varnode_write_class(_Varnode(_Space("ram", False))) is None
    assert tracer.ram_varnode_write_class(_Varnode(_Space("register", True))) is None
    assert tracer.calls == [0x1000d0]
