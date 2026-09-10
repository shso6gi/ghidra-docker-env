"""UNKNOWN cause taxonomy の浮動小数点証拠が object-derived であることを固定する。

`_expression_uses_float_or_float_op` は判定 gate ではなく、既に UNKNOWN と
なった pair の cause / recovery 分類に使われる。ここでは「シンボル名や型名の
部分一致を根拠にしない」ことと、採用する 3 系統の証拠が実際に効くことを固定
する。
"""

from enum import Enum, auto

from scripts.function_tracer_pcode.core import Expression
from unittest.mock import Mock

from scripts.function_tracer_pcode.core.call_target import (
    CallTargetRef,
    call_target_declared_return_data_types,
    call_target_returns_floating_value,
)
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.core.render_smt import (
    FLOAT_SEMANTICS_PCODE_OPERATORS,
    _FLOAT_ARITHMETIC_SMT_NAMES,
    _FLOAT_PREDICATE_SMT_NAMES,
    _FLOAT_UNARY_PREDICATE_SMT_NAMES,
    _FLOAT_UNARY_VALUE_SMT_NAMES,
    _SUPPORTED_BINARY_OPERATORS,
    _SUPPORTED_UNARY_OPERATORS,
)
from scripts.function_tracer_pcode.core.runtime_refs import DeferredCallRef, UnknownValueRef
from scripts.function_tracer_pcode.proof.strategies.pairwise_services.auxiliary_smt import (
    _impl__expression_uses_float_or_float_op as uses_float,
)


class _StubDataTypeManager:
    """Ghidra 無しで float DataType 候補を返す DataTypeManager 代用。"""

    def __init__(self):
        self.float_data_types = []

    def getFloatDataTypes(self):
        return list(self.float_data_types)


class _StubDataType:
    def __init__(self, type_name, manager):
        self._type_name = type_name
        self._manager = manager

    def getDataTypeManager(self):
        return self._manager

    def isEquivalent(self, other):
        return isinstance(other, _StubDataType) and other._type_name == self._type_name


class _StubVoidDataType:
    """getLength() == 0 で void と判定される DataType 代用。"""

    def getLength(self):
        return 0


class _StubUndefinedDataType:
    def isUndefined(self):
        return True

    def getLength(self):
        return 4


class _StubFunction:
    def __init__(self, return_type, thunked=None):
        self._return_type = return_type
        self._thunked = thunked

    def getReturnType(self):
        return self._return_type

    def getThunkedFunction(self, *args):
        return self._thunked


def _float_and_int_data_types():
    manager = _StubDataTypeManager()
    double_type = _StubDataType("double", manager)
    int_type = _StubDataType("int", manager)
    manager.float_data_types = [double_type]
    return double_type, int_type


def _double_param(name="x"):
    double_type, _ = _float_and_int_data_types()
    return Expression.parameter(name, 0, data_type="double", data_type_obj=double_type, size=8)


def _int_param(name="n"):
    _, int_type = _float_and_int_data_types()
    return Expression.parameter(name, 0, data_type="int", data_type_obj=int_type, size=4)


def _deferred_call_expression(target_ref):
    """tracer が作る deferred-call UNKNOWN と同じ形にする。

    ``tracer_calls`` は ``DeferredCallRef.display_name()`` を式の name にするので、
    アドレスを持たない deferred call の name はシンボル名そのもの（``"log"``）に
    なる。撤去した名前一致が実際に発火していたのはこの形。
    """
    deferred_call_ref = DeferredCallRef(target_ref=target_ref)
    return Expression.unknown(
        deferred_call_ref.display_name(),
        runtime_ref=UnknownValueRef.deferred_call(
            deferred_call_ref=deferred_call_ref,
            target_ref=target_ref,
        ),
    ).clone_with(size=8)


def _float_returning_target(function_name="anonymous_external"):
    double_type, _ = _float_and_int_data_types()
    return CallTargetRef(
        kind="function",
        function_name=function_name,
        is_external=True,
        function_obj=_StubFunction(double_type),
    )


def _phi_circular_unknown(binary_id="B1", entry=0x1000):
    pcode_ref = PcodeOpRef(
        address_offset=entry + 0x1C,
        seq_time=98,
        seq_order=0,
        block_index=0,
        mnemonic="MULTIEQUAL",
        input_sizes=(4, 4),
        output_size=4,
        binary_id=binary_id,
        function_entry_space="ram",
        function_entry_offset=entry,
        target_space="ram",
        target_offset=entry + 0x1C,
        opcode=60,
        local_op_ordinal=0,
    )
    return Expression.unknown(
        "phi_circular",
        runtime_ref=UnknownValueRef.phi_circular(pcode_op_ref=pcode_ref),
    ).clone_with(size=4)


def _classification(expr, location_scope="return_value"):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    return strategy, strategy._unresolved_expression_location_classification(expr, location_scope)


def _label(classification, field):
    for item in classification:
        if isinstance(item, tuple) and len(item) == 2 and item[0] == field:
            return item[1]
    return None


# --- 名前一致は根拠にしない -------------------------------------------------


def test_libm_symbol_name_alone_is_not_float_evidence():
    for symbol in ("log", "exp", "sqrt", "sin", "cos", "pow"):
        call_expr = Expression.call(symbol, [_int_param()])
        assert uses_float(call_expr) is False, symbol


def test_libm_symbol_name_on_variable_or_intrinsic_is_not_float_evidence():
    assert uses_float(Expression.variable("log", data_type="int", size=4)) is False
    assert uses_float(Expression.intrinsic("sqrt", [_int_param()], size=4)) is False


def test_deferred_call_named_like_libm_without_typed_signature_is_not_float_evidence():
    target_ref = CallTargetRef(kind="function", function_name="log", is_external=True)
    assert uses_float(_deferred_call_expression(target_ref)) is False


def test_expression_type_name_substring_is_not_float_evidence():
    class _TypeNameLooksFloaty(Enum):
        FLOATY_LOOKING = auto()
        PHI = auto()

    class _Node:
        expr_type = _TypeNameLooksFloaty.FLOATY_LOOKING
        operator = None
        name = "F"
        operands = ()
        value = None
        runtime_ref = None
        data_type_obj = None

    assert uses_float(_Node()) is False


def test_integer_operators_are_not_float_evidence():
    int_expr = Expression.binary_op("INT_ADD", _int_param(), Expression.constant(1, size=4))
    assert uses_float(int_expr) is False
    assert uses_float(Expression.unary_op("TRUNC", _int_param())) is False
    assert uses_float(None) is False


# --- P-code opcode 証拠 ------------------------------------------------------


def test_float_pcode_operators_are_float_evidence():
    for operator in ("FLOAT_ADD", "FLOAT_MULT", "FLOAT_LESS"):
        expr = Expression.binary_op(
            operator,
            Expression.constant(1, size=8),
            Expression.constant(2, size=8),
        )
        assert uses_float(expr) is True, operator
    for operator in ("FLOAT_SQRT", "FLOAT_ABS", "INT2FLOAT", "FLOAT2FLOAT"):
        expr = Expression.unary_op(operator, Expression.constant(1, size=8))
        assert uses_float(expr) is True, operator


def test_float_pcode_operator_nested_under_phi_is_float_evidence():
    from scripts.function_tracer_pcode.core import Condition

    float_expr = Expression.unary_op("FLOAT_ABS", Expression.constant(1, size=8))
    phi = Expression.phi([
        (Condition(Expression.constant(1, size=1)), float_expr),
        (None, Expression.constant(0, size=8)),
    ])
    assert uses_float(phi) is True


def test_float_operator_registry_covers_every_rendered_float_operator():
    rendered = (
        set(_FLOAT_PREDICATE_SMT_NAMES)
        | set(_FLOAT_ARITHMETIC_SMT_NAMES)
        | set(_FLOAT_UNARY_PREDICATE_SMT_NAMES)
        | set(_FLOAT_UNARY_VALUE_SMT_NAMES)
        | {op for op in _SUPPORTED_BINARY_OPERATORS if "FLOAT" in op}
        | {op for op in _SUPPORTED_UNARY_OPERATORS if "FLOAT" in op}
    )
    assert rendered <= FLOAT_SEMANTICS_PCODE_OPERATORS


# --- 型情報 / typed provenance 証拠 ------------------------------------------


def test_declared_float_parameter_type_is_float_evidence():
    assert uses_float(_double_param()) is True


def test_declared_integer_parameter_type_is_not_float_evidence():
    assert uses_float(_int_param()) is False


def test_declared_float_type_nested_in_integer_operator_is_float_evidence():
    expr = Expression.binary_op("INT_ADD", _double_param(), Expression.constant(1, size=8))
    assert uses_float(expr) is True


def test_call_target_with_declared_float_return_type_is_float_evidence():
    target_ref = _float_returning_target()
    assert call_target_returns_floating_value(target_ref) is True
    assert uses_float(_deferred_call_expression(target_ref)) is True


def test_call_target_with_declared_integer_return_type_is_not_float_evidence():
    _, int_type = _float_and_int_data_types()
    target_ref = CallTargetRef(
        kind="function",
        function_name="log",
        is_external=True,
        function_obj=_StubFunction(int_type),
    )
    assert call_target_returns_floating_value(target_ref) is False
    assert uses_float(_deferred_call_expression(target_ref)) is False


def test_call_target_without_resolved_function_is_not_float_evidence():
    assert call_target_returns_floating_value(CallTargetRef.unknown()) is False
    assert call_target_returns_floating_value(None) is False


# --- thunk の戻り型 provenance ---------------------------------------------


def test_thunk_target_return_type_is_used_when_wrapper_has_none():
    double_type, _ = _float_and_int_data_types()
    thunk = _StubFunction(None, thunked=_StubFunction(double_type))
    target_ref = CallTargetRef(
        kind="function",
        function_name="thunk_to_external",
        is_thunk=True,
        thunked_is_external=True,
        function_obj=thunk,
    )
    assert call_target_declared_return_data_types(target_ref) == (double_type,)
    assert call_target_returns_floating_value(target_ref) is True
    assert uses_float(_deferred_call_expression(target_ref)) is True


def test_thunk_target_return_type_is_used_when_wrapper_declares_void_or_undefined():
    double_type, _ = _float_and_int_data_types()
    for insufficient in (_StubVoidDataType(), _StubUndefinedDataType()):
        thunk = _StubFunction(insufficient, thunked=_StubFunction(double_type))
        target_ref = CallTargetRef(
            kind="function",
            function_name="thunk_to_external",
            is_thunk=True,
            function_obj=thunk,
        )
        # void / undefined は「宣言が無い」扱いなので候補に残らない。
        assert call_target_declared_return_data_types(target_ref) == (double_type,)
        assert call_target_returns_floating_value(target_ref) is True


def test_thunk_and_wrapper_agreeing_on_float_is_float_evidence():
    double_type, _ = _float_and_int_data_types()
    thunk = _StubFunction(double_type, thunked=_StubFunction(double_type))
    target_ref = CallTargetRef(kind="function", function_name="t", is_thunk=True, function_obj=thunk)
    assert len(call_target_declared_return_data_types(target_ref)) == 2
    assert call_target_returns_floating_value(target_ref) is True


def test_thunk_and_wrapper_disagreeing_on_floatness_is_not_float_evidence():
    double_type, int_type = _float_and_int_data_types()
    # thunk target だけが double。wrapper は int を宣言している。
    thunk = _StubFunction(int_type, thunked=_StubFunction(double_type))
    target_ref = CallTargetRef(kind="function", function_name="t", is_thunk=True, function_obj=thunk)
    assert call_target_declared_return_data_types(target_ref) == (double_type, int_type)
    assert call_target_returns_floating_value(target_ref) is False
    assert uses_float(_deferred_call_expression(target_ref)) is False

    # 逆向きも同じく証拠にしない。
    thunk = _StubFunction(double_type, thunked=_StubFunction(int_type))
    target_ref = CallTargetRef(kind="function", function_name="t", is_thunk=True, function_obj=thunk)
    assert call_target_returns_floating_value(target_ref) is False


def test_thunk_and_wrapper_agreeing_on_non_float_is_not_float_evidence():
    _, int_type = _float_and_int_data_types()
    thunk = _StubFunction(int_type, thunked=_StubFunction(int_type))
    target_ref = CallTargetRef(kind="function", function_name="t", is_thunk=True, function_obj=thunk)
    assert call_target_returns_floating_value(target_ref) is False


# --- taxonomy / recovery obligation まで通す --------------------------------


def test_named_libm_deferred_call_without_types_lands_in_deferred_call_return():
    """型情報の無い deferred ``log`` が名前だけで float 系 taxonomy に行かない。"""
    target_ref = CallTargetRef(kind="function", function_name="log", is_external=True)
    expr = _deferred_call_expression(target_ref)
    assert expr.name == "log"  # 撤去した名前一致が発火していた形

    strategy, classification = _classification(expr)

    assert _label(classification, "unresolved_cause") == "deferred_call_return"
    assert _label(classification, "unresolved_substage") == "deferred_call_return_value_pending"
    assert strategy._unresolved_expression_target_uses_generic_pending_census(classification) is False
    assert strategy._unresolved_expression_generic_diagnostic_evidence(classification) is None


def test_deferred_call_with_declared_float_return_type_lands_in_float_taxonomy():
    expr = _deferred_call_expression(_float_returning_target("anonymous_external"))

    strategy, classification = _classification(expr)

    assert _label(classification, "unresolved_cause") == "mixed_float_call_read_recurrence"
    assert (
        _label(classification, "unresolved_substage")
        == "mixed_float_call_read_recurrence_deferred"
    )
    assert strategy._unresolved_expression_target_uses_generic_pending_census(classification) is True
    evidence = strategy._unresolved_expression_generic_diagnostic_evidence(classification)
    assert evidence is not None
    assert ("unresolved_cause", "mixed_float_call_read_recurrence") in evidence


def test_float_typed_operand_beside_deferred_call_lands_in_float_taxonomy():
    """opcode が整数でも、宣言型が double なら float 系 taxonomy に入る。"""
    target_ref = CallTargetRef(kind="function", function_name="helper", is_external=True)
    expr = Expression.binary_op("INT_ADD", _double_param(), _deferred_call_expression(target_ref))

    _strategy, classification = _classification(expr)

    assert _label(classification, "unresolved_cause") == "mixed_float_call_read_recurrence"


def test_libm_named_variable_no_longer_suppresses_phi_circular_recovery():
    """名前一致撤去で ``phi_circular_integer`` の recovery が不当に抑止されない。"""
    _, int_type = _float_and_int_data_types()
    # 名前が libm 風なだけの整数変数。撤去前はこれだけで has_float が立ち、
    # phi_circular_integer が mixed_float_call_read_recurrence に潰されていた。
    named_like_libm = Expression.variable(
        "log",
        data_type="int",
        data_type_obj=int_type,
        size=4,
    )
    guard_expr = Expression.binary_op("INT_SLESS", _phi_circular_unknown(), named_like_libm)

    strategy, classification = _classification(guard_expr, "guard_condition")

    assert _label(classification, "unresolved_cause") == "phi_circular_integer"
    assert (
        _label(classification, "unresolved_substage")
        == "integer_phi_circular_guard_pending"
    )
    assert strategy._unresolved_expression_target_uses_generic_pending_census(classification) is False

    obligations = strategy._unresolved_expression_recovery_proof_obligations(classification)
    assert obligations is not None
    assert "phi_circular_guard_condition_lowering" in {
        obligation.proof_stage for obligation in obligations
    }


def test_float_typed_phi_circular_guard_still_leaves_the_integer_phi_lane():
    """型が double なら、名前ではなく型を根拠に整数 phi lane から外れる。"""
    guard_expr = Expression.binary_op("INT_SLESS", _phi_circular_unknown(), _double_param())

    _strategy, classification = _classification(guard_expr, "guard_condition")

    assert _label(classification, "unresolved_cause") == "mixed_float_call_read_recurrence"
