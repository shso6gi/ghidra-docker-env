"""Issue #31: -INT_MIN UB constraints must cover guards and signed non-parameter operands."""
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.proof.ub.constraints import UbConstraintBuilder
from scripts.function_tracer_pcode.tests.unit._publication import published


def _param(name, size=4):
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


def _const(value, size=4):
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _neg(expr):
    return Expression(ExpressionType.UNARY_OP, operator="INT_2COMP", operands=[expr], size=expr.size)


def _slt(left, right):
    return Expression(ExpressionType.BINARY_OP, operator="INT_SLESS", operands=[left, right], size=1)


def _ult(left, right):
    return Expression(ExpressionType.BINARY_OP, operator="INT_LESS", operands=[left, right], size=1)


def _mul(left, right):
    return Expression(ExpressionType.BINARY_OP, operator="INT_MULT", operands=[left, right], size=left.size)


def _analysis(returns, params):
    # test がこの解析の producer。組み立て終えたここで公開する。
    return published(
        FunctionReturnAnalysis(
            function_name="snippet",
            entry_point="0x1000",
            parameters=[{"name": p.original_name, "size": p.bit_width // 8, "index": p.index, "is_signed": p.is_signed} for p in params],
            returns=returns,
        )
    )


def _infos(*specs):
    return [
        ParameterInfo(original_name=name, smt_name=f"{name}_1", bit_width=bits, index=i, is_signed=signed)
        for i, (name, bits, signed) in enumerate(specs)
    ]


def _replace(expr_or_text):
    text = expr_or_text if isinstance(expr_or_text, str) else expr_or_text.to_smt()
    return text.replace("param_1", "param_1_1").replace("param_2", "param_2_1")


def test_negated_signed_parameter_inside_a_guard_gets_int_min_constraint():
    # pow/test shape: if (-y < -8) ... with y == INT_MIN being UB.
    infos = _infos(("param_1", 32, True), ("param_2", 32, True))
    guard = Condition(_slt(_neg(_param("param_2")), _const(0xFFFFFFF8)))
    analysis = _analysis([ReturnInfo(address="0x1", value=_const(3), conditions=[guard])], infos)

    constraints = UbConstraintBuilder().build_constraints(analysis, infos, {"negate_min"}, _replace)

    assert "(assert (not (= param_2_1 (_ bv2147483648 32))))" in constraints
    assert len([c for c in constraints if c.startswith("(assert")]) == 1


def test_negated_unsigned_parameter_is_defined_behaviour_and_not_constrained():
    infos = _infos(("param_1", 32, False))
    analysis = _analysis(
        [ReturnInfo(address="0x1", value=_neg(_param("param_1")), conditions=[])], infos
    )

    assert UbConstraintBuilder().build_constraints(analysis, infos, {"negate_min"}, _replace) == []


def test_negated_signed_parameter_in_return_value_still_constrained():
    infos = _infos(("param_1", 64, True))
    analysis = _analysis(
        [ReturnInfo(address="0x1", value=_neg(_param("param_1", size=8)), conditions=[])], infos
    )

    constraints = UbConstraintBuilder().build_constraints(analysis, infos, {"negate_min"}, _replace)

    assert "(assert (not (= param_1_1 (_ bv9223372036854775808 64))))" in constraints


def test_negated_compound_operand_is_constrained_only_in_signed_context():
    infos = _infos(("param_1", 32, True))
    product = _mul(_param("param_1"), _param("param_1"))

    signed_guard = Condition(_slt(_neg(product), _const(0xFFFFFFF8)))
    signed = _analysis([ReturnInfo(address="0x1", value=_const(1), conditions=[signed_guard])], infos)
    constraints = UbConstraintBuilder().build_constraints(signed, infos, {"negate_min"}, _replace)
    asserts = [c for c in constraints if c.startswith("(assert")]
    assert len(asserts) == 1
    assert "param_1_1" in asserts[0] and "(_ bv2147483648 32)" in asserts[0]

    unsigned_guard = Condition(_ult(_neg(product), _const(8)))
    unsigned = _analysis([ReturnInfo(address="0x1", value=_const(1), conditions=[unsigned_guard])], infos)
    assert UbConstraintBuilder().build_constraints(unsigned, infos, {"negate_min"}, _replace) == []


def test_duplicate_negation_sites_emit_a_single_constraint():
    infos = _infos(("param_1", 32, True), ("param_2", 32, True))
    guard = Condition(_slt(_neg(_param("param_2")), _const(0xFFFFFFF8)))
    other = Condition(_slt(_neg(_param("param_2")), _const(0)))
    analysis = _analysis(
        [
            ReturnInfo(address="0x1", value=_neg(_param("param_2")), conditions=[guard]),
            ReturnInfo(address="0x2", value=_const(0), conditions=[other]),
        ],
        infos,
    )

    constraints = UbConstraintBuilder().build_constraints(analysis, infos, {"negate_min"}, _replace)

    assert [c for c in constraints if c.startswith("(assert")] == [
        "(assert (not (= param_2_1 (_ bv2147483648 32))))"
    ]
