"""UNKNOWN cause taxonomy の浮動小数点証拠が object-derived であることを固定する。

`_expression_uses_float_or_float_op` は判定 gate ではなく、既に UNKNOWN と
なった pair の cause / recovery 分類に使われる。ここでは「シンボル名や型名の
部分一致を根拠にしない」ことと、採用する 3 系統の証拠が実際に効くことを固定
する。
"""

from enum import Enum, auto

from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.core.call_target import (
    CallTargetRef,
    call_target_returns_floating_value,
)
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


class _StubFunction:
    def __init__(self, return_type):
        self._return_type = return_type

    def getReturnType(self):
        return self._return_type


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
    return Expression.unknown(
        "deferred_call",
        runtime_ref=UnknownValueRef.deferred_call(
            deferred_call_ref=DeferredCallRef(target_ref=target_ref),
            target_ref=target_ref,
        ),
    )


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
    double_type, _ = _float_and_int_data_types()
    target_ref = CallTargetRef(
        kind="function",
        function_name="anonymous_external",
        is_external=True,
        function_obj=_StubFunction(double_type),
    )
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
