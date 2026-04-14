# -*- coding: utf-8 -*-

import re

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.model.analysis import FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.model.condition import Condition
from scripts.function_tracer_pcode.model.expression import Expression


def _make_analyzer():
    analyzer = ReturnAnalyzer(None, debug=False)
    return analyzer


def _evaluate_expression(expr, env):
    def bits(node):
        return max(1, (getattr(node, "size", 0) or 4) * 8)

    def mask(width):
        return (1 << width) - 1

    def signed(value, width):
        sign = 1 << (width - 1)
        return value - (1 << width) if value & sign else value

    expr_type = expr.expr_type.name
    if expr_type == "CONSTANT":
        return int(expr.value)
    if expr_type in {"PARAMETER", "VARIABLE"}:
        return int(env[expr.name])
    if expr_type == "UNARY_OP":
        operand = _evaluate_expression(expr.operands[0], env)
        if expr.operator in {"INT_2COMP", "INT_NEGATE"}:
            return -operand
        if expr.operator == "BOOL_NEGATE":
            return int(not operand)
        if expr.operator == "COPY":
            return operand
        if expr.operator == "INT_SEXT":
            source_width = bits(expr.operands[0])
            return signed(operand & mask(source_width), source_width)
        if expr.operator == "INT_ZEXT":
            source_width = bits(expr.operands[0])
            return operand & mask(source_width)
        raise AssertionError(f"unsupported unary operator: {expr.operator}")
    if expr_type == "PHI":
        for condition, value in expr.value:
            if condition is None or _evaluate_condition(condition, env):
                return _evaluate_expression(value, env)
        raise AssertionError("no PHI branch selected")
    if expr_type == "BINARY_OP":
        left = _evaluate_expression(expr.operands[0], env)
        right = _evaluate_expression(expr.operands[1], env)
        if expr.operator == "PIECE":
            low_bits = max(1, (getattr(expr.operands[1], "size", 0) or 4) * 8)
            return (left << low_bits) | right
        if expr.operator == "SUBPIECE":
            shift_bytes = int(right)
            width = bits(expr)
            return (left >> (shift_bytes * 8)) & mask(width)
        if expr.operator == "INT_ADD":
            return left + right
        if expr.operator == "INT_SUB":
            return left - right
        if expr.operator == "INT_MULT":
            return left * right
        if expr.operator in {"INT_SDIV", "INT_DIV"}:
            assert right != 0
            return int(left / right)
        if expr.operator == "INT_AND":
            return left & right
        if expr.operator in {"INT_SRIGHT", "INT_RIGHT"}:
            return left >> right
        if expr.operator in {"INT_SLESS", "INT_LESS"}:
            return int(left < right)
        if expr.operator in {"INT_SLESSEQUAL", "INT_LESSEQUAL"}:
            return int(left <= right)
        if expr.operator == "INT_EQUAL":
            return int(left == right)
        if expr.operator == "INT_NOTEQUAL":
            return int(left != right)
        if expr.operator == "BOOL_AND":
            return int(bool(left) and bool(right))
        if expr.operator == "BOOL_OR":
            return int(bool(left) or bool(right))
        raise AssertionError(f"unsupported binary operator: {expr.operator}")
    raise AssertionError(f"unsupported expression type: {expr_type}")


def _evaluate_condition(condition, env):
    truth = bool(_evaluate_expression(condition.expression, env))
    return not truth if condition.negated else truth


def _select_return_value(recovered, env):
    matching = [
        ret for ret in recovered
        if all(_evaluate_condition(cond, env) for cond in ret.conditions)
    ]
    assert matching
    values = [_evaluate_expression(ret.value, env) for ret in matching]
    assert all(value == values[0] for value in values[1:])
    return values[0]


def _expected_nested_multiply_accumulate(rows, cols):
    acc = 0
    for i in range(max(rows, 0)):
        for j in range(max(cols, 0)):
            acc += (i + 1) * (j + 1)
    return acc


def _expected_nested_multiply_accumulate_wrapped_32(rows, cols):
    modulus = 1 << 32
    triangular_rows = (max(rows, 0) * (max(rows, 0) + 1) // 2) % modulus
    triangular_cols = (max(cols, 0) * (max(cols, 0) + 1) // 2) % modulus
    return (triangular_rows * triangular_cols) % modulus


def _evaluate_expression_wrapped(expr, env):
    def bits(node):
        return max(1, (getattr(node, "size", 0) or 4) * 8)

    def mask(width):
        return (1 << width) - 1

    def signed(value, width):
        sign = 1 << (width - 1)
        return value - (1 << width) if value & sign else value

    expr_type = expr.expr_type.name
    if expr_type == "CONSTANT":
        width = bits(expr)
        return int(expr.value) & mask(width)
    if expr_type in {"PARAMETER", "VARIABLE"}:
        width = bits(expr)
        return int(env[expr.name]) & mask(width)
    if expr_type == "UNARY_OP":
        operand = _evaluate_expression_wrapped(expr.operands[0], env)
        width = bits(expr)
        current_mask = mask(width)
        if expr.operator in {"INT_2COMP", "INT_NEGATE"}:
            return (-operand) & mask(width)
        if expr.operator == "COPY":
            return operand & current_mask
        if expr.operator == "INT_SEXT":
            source_width = bits(expr.operands[0])
            return signed(operand & mask(source_width), source_width) & current_mask
        if expr.operator == "INT_ZEXT":
            source_width = bits(expr.operands[0])
            return operand & mask(source_width) & current_mask
        raise AssertionError(f"unsupported wrapped unary operator: {expr.operator}")
    if expr_type == "PHI":
        for condition, value in expr.value:
            if condition is None or _evaluate_condition_wrapped(condition, env):
                return _evaluate_expression_wrapped(value, env)
        raise AssertionError("no wrapped PHI branch selected")
    if expr_type == "BINARY_OP":
        left = _evaluate_expression_wrapped(expr.operands[0], env)
        right = _evaluate_expression_wrapped(expr.operands[1], env)
        width = bits(expr)
        current_mask = mask(width)
        if expr.operator == "PIECE":
            low_bits = max(1, (getattr(expr.operands[1], "size", 0) or 4) * 8)
            return ((left << low_bits) | right) & current_mask
        if expr.operator == "SUBPIECE":
            shift_bytes = int(right)
            return (left >> (shift_bytes * 8)) & current_mask
        if expr.operator == "INT_ADD":
            return (left + right) & current_mask
        if expr.operator == "INT_SUB":
            return (left - right) & current_mask
        if expr.operator == "INT_MULT":
            return (left * right) & current_mask
        if expr.operator == "INT_AND":
            return (left & right) & current_mask
        if expr.operator == "INT_RIGHT":
            return (left >> right) & current_mask
        if expr.operator == "INT_SRIGHT":
            return (signed(left, width) >> right) & current_mask
        if expr.operator in {"INT_SDIV", "INT_DIV"}:
            assert right != 0
            return int(signed(left, width) / signed(right, width)) & current_mask
        if expr.operator in {"INT_SLESS", "INT_LESS"}:
            return int(signed(left, width) < signed(right, width))
        if expr.operator in {"INT_SLESSEQUAL", "INT_LESSEQUAL"}:
            return int(signed(left, width) <= signed(right, width))
        if expr.operator == "INT_EQUAL":
            return int(left == right)
        if expr.operator == "INT_NOTEQUAL":
            return int(left != right)
        raise AssertionError(f"unsupported wrapped binary operator: {expr.operator}")
    raise AssertionError(f"unsupported wrapped expression type: {expr_type}")


def _evaluate_condition_wrapped(condition, env):
    truth = bool(_evaluate_expression_wrapped(condition.expression, env))
    return not truth if condition.negated else truth


def _select_return_value_wrapped(recovered, env):
    matching = [
        ret for ret in recovered
        if all(_evaluate_condition_wrapped(cond, env) for cond in ret.conditions)
    ]
    assert matching
    values = [_evaluate_expression_wrapped(ret.value, env) for ret in matching]
    assert all(value == values[0] for value in values[1:])
    return values[0]


def _select_return_value_wrapped32(recovered, env):
    return _select_return_value_wrapped(recovered, env) & 0xFFFFFFFF


def _assert_no_variable_name(expr_text, variable_name):
    assert re.search(rf"\\b{re.escape(variable_name)}\\b", expr_text) is None


def _expected_triangular_step_sum(n):
    acc = 0
    step = 1
    for _ in range(max(n, 0)):
        acc += step
        step += 1
    return acc


def test_structured_reduction_recovery_recovers_nested_multiply_accumulate():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "rows", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "cols", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int rows, int cols) {
    int acc = 0;
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            acc += (i + 1) * (j + 1);
        }
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert len(recovered) == 3
    positive_case = next(
        ret
        for ret in recovered
        if any(cond.to_string() == "(0 < rows)" for cond in ret.conditions)
        and any(cond.to_string() == "(0 < cols)" for cond in ret.conditions)
    )
    assert "rows" in positive_case.value.to_string()
    assert "cols" in positive_case.value.to_string()
    _assert_no_variable_name(positive_case.value.to_string(), "i")
    _assert_no_variable_name(positive_case.value.to_string(), "j")
    assert "UNKNOWN" not in positive_case.value.to_string()

    for rows in range(-1, 5):
        for cols in range(-1, 5):
            env = {"rows": rows, "cols": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_structured_reduction_recovery_recovers_triangular_count():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_triangular_count(int n) {
    int count = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j <= i; j++) {
            count += 1;
        }
    }
    return count;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert len(recovered) == 2
    positive_case = next(
        ret
        for ret in recovered
        if any(cond.to_string() == "(0 < n)" for cond in ret.conditions)
    )
    assert "n" in positive_case.value.to_string()
    _assert_no_variable_name(positive_case.value.to_string(), "i")
    _assert_no_variable_name(positive_case.value.to_string(), "j")
    assert "UNKNOWN" not in positive_case.value.to_string()


def test_structured_reduction_recovery_handles_if_guarded_loops():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "rows", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "cols", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int rows, int cols) {
    int acc = 0;
    if (0 < rows) {
        if (0 < cols) {
            for (int i = 0; i < rows; i++) {
                for (int j = 0; j < cols; j++) {
                    acc += (i + 1) * (j + 1);
                }
            }
        }
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert len(recovered) == 3
    for rows in range(-1, 5):
        for cols in range(-1, 5):
            env = {"rows": rows, "cols": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_structured_reduction_recovery_handles_nested_while_loops():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "rows", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "cols", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int rows, int cols) {
    int acc = 0;
    int i = 0;
    while (i < rows) {
        int j = 0;
        while (j < cols) {
            acc += (i + 1) * (j + 1);
            j++;
        }
        i++;
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for rows in range(-1, 5):
        for cols in range(-1, 5):
            env = {"rows": rows, "cols": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_structured_reduction_recovery_handles_guarded_do_while_loops():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "rows", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "cols", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int rows, int cols) {
    int acc = 0;
    if (0 < rows) {
        int i = 0;
        do {
            if (0 < cols) {
                int j = 0;
                do {
                    acc += (i + 1) * (j + 1);
                    j++;
                } while (j != cols);
            }
            i++;
        } while (i != rows);
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for rows in range(-1, 5):
        for cols in range(-1, 5):
            env = {"rows": rows, "cols": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_structured_reduction_recovery_handles_loop_carried_helper_induction_variable():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_triangular_step_sum(int n) {
    int acc = 0;
    int step = 1;
    for (int i = 0; i < n; i++) {
        acc += step;
        step++;
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    positive_case = next(
        ret
        for ret in recovered
        if any(cond.to_string() == "(0 < n)" for cond in ret.conditions)
    )
    _assert_no_variable_name(positive_case.value.to_string(), "step")
    _assert_no_variable_name(positive_case.value.to_string(), "i")
    for n in range(-1, 7):
        env = {"n": n}
        assert _select_return_value(recovered, env) == _expected_triangular_step_sum(n)


def test_structured_reduction_recovery_handles_decrementing_remaining_counter_with_helper_step():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int acc;
  int step;
  long remaining;
  remaining = param_1;
  if (0 < remaining) {
    acc = 0;
    step = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    do {
      acc = acc + step;
      step = step + (param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1);
      remaining = remaining - 1;
    } while (0 < remaining);
  }
  else {
    acc = 0;
  }
  return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for rows in range(-1, 5):
        for cols in range(-1, 5):
            env = {"param_1": rows, "param_2": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_structured_reduction_recovery_handles_clang_like_countdown_helper_loop():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "long", "size": 8, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,long param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  int iVar4;
  if (0 < param_1) {
    iVar4 = (int)param_2;
    iVar2 = 0;
    iVar3 = iVar4 * 2 + (int)((ulong)(iVar4 - 1) * (ulong)(iVar4 - 2) >> 1) + -1;
    iVar4 = iVar3;
    do {
      iVar1 = iVar4 + iVar3;
      if (param_2 < 1) {
        iVar4 = 0;
      }
      iVar2 = iVar2 + iVar4;
      param_1 = param_1 + -1;
      iVar4 = iVar1;
    } while (param_1 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for rows in range(-1, 6):
        for cols in range(-1, 6):
            env = {"param_1": rows, "param_2": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_structured_reduction_recovery_preserves_large_width_wrapped_triangular_sum():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "long", "size": 8, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,long param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  int iVar4;
  if (0 < param_1) {
    iVar4 = (int)param_2;
    iVar2 = 0;
    iVar3 = iVar4 * 2 + (int)((ulong)(iVar4 - 1) * (ulong)(iVar4 - 2) >> 1) + -1;
    iVar4 = iVar3;
    do {
      iVar1 = iVar4 + iVar3;
      if (param_2 < 1) {
        iVar4 = 0;
      }
      iVar2 = iVar2 + iVar4;
      param_1 = param_1 + -1;
      iVar4 = iVar1;
    } while (param_1 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    env = {"param_1": 2147483410, "param_2": 1993640592}
    assert _select_return_value_wrapped32(recovered, env) == _expected_nested_multiply_accumulate_wrapped_32(
        env["param_1"],
        env["param_2"],
    )


def test_structured_reduction_recovery_preserves_large_width_wrapped_nested_do_while_sum():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  bool bVar1;
  int iVar2;
  int iVar3;
  int iVar4;
  int iVar5;
  if (param_1 < 1) {
    iVar2 = 0;
  }
  else {
    iVar4 = 1;
    iVar2 = 0;
    do {
      if (0 < param_2) {
        iVar3 = 0;
        iVar5 = iVar4;
        do {
          iVar3 = iVar3 + 1;
          iVar2 = iVar5 + iVar2;
          iVar5 = iVar5 + iVar4;
        } while (iVar3 != param_2);
      }
      bVar1 = iVar4 != param_1;
      iVar4 = iVar4 + 1;
    } while (bVar1);
  }
  return iVar2;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert _select_return_value_wrapped32(recovered, {"param_1": 1, "param_2": 2}) == 3
    env = {"param_1": 2147483410, "param_2": 1993640592}
    assert _select_return_value_wrapped32(recovered, env) == _expected_nested_multiply_accumulate_wrapped_32(
        env["param_1"],
        env["param_2"],
    )


def test_structured_reduction_recovery_handles_bool_alias_do_while_condition():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_triangular_step_sum_alias(int n) {
    bool cont;
    int acc = 0;
    int step = 1;
    if (0 < n) {
        do {
            acc += step;
            cont = step != n;
            step++;
        } while (cont);
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    positive_case = next(
        ret
        for ret in recovered
        if any(cond.to_string() == "(0 < n)" for cond in ret.conditions)
    )
    assert "cont" not in positive_case.value.to_string()
    _assert_no_variable_name(positive_case.value.to_string(), "step")
    for n in range(-1, 7):
        env = {"n": n}
        assert _select_return_value(recovered, env) == _expected_triangular_step_sum(n)


def test_structured_reduction_recovery_handles_shared_bool_alias_and_ephemeral_inner_temps():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  bool bVar1;
  int iVar2;
  int iVar3;
  int iVar4;
  int iVar5;
  if (param_1 < 1) {
    iVar2 = 0;
  }
  else {
    iVar4 = 1;
    iVar2 = 0;
    do {
      if (0 < param_2) {
        iVar5 = 1;
        iVar3 = 0;
        do {
          iVar3 = iVar3 + iVar4 * iVar5;
          bVar1 = iVar5 != param_2;
          iVar5 = iVar5 + 1;
        } while (bVar1);
        iVar2 = iVar2 + iVar3;
      }
      bVar1 = iVar4 != param_1;
      iVar4 = iVar4 + 1;
    } while (bVar1);
  }
  return iVar2;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    positive_cases = [
        ret
        for ret in recovered
        if any(cond.to_string() == "(0 < param_2)" for cond in ret.conditions)
        and any(cond.to_string() == "(not (param_1 < 1))" for cond in ret.conditions)
    ]
    assert positive_cases
    for positive_case in positive_cases:
        assert "iVar3" not in positive_case.value.to_string()
        assert "iVar5" not in positive_case.value.to_string()
        assert "bVar1" not in positive_case.value.to_string()
    for rows in range(-1, 5):
        for cols in range(-1, 5):
            env = {"param_1": rows, "param_2": cols}
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_parse_wrapper_expr_accepts_concat_of_declared_fragment_and_parameter():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    expr = analyzer._parse_wrapper_expr(
        "CONCAT44(in_a0_hi,param_1)",
        parameters,
        fallback_index=0,
        local_bindings={
            "in_a0_hi": Expression.variable("in_a0_hi", data_type="undefined4", size=4),
        },
    )

    assert expr is not None
    assert expr.operator == "PIECE"
    assert expr.size == 8
    assert expr.operands[0].name == "in_a0_hi"
    assert expr.operands[1].name == "param_1"


def test_parse_wrapper_expr_keeps_shift_operators_distinct_from_comparisons():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_2", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]

    shifted = analyzer._parse_wrapper_expr("param_2 >> 1", parameters, fallback_index=0, local_bindings={})
    multiplied = analyzer._parse_wrapper_expr(
        "((param_2 - 1) * (param_2 - 2)) >> 1",
        parameters,
        fallback_index=0,
        local_bindings={},
    )

    assert shifted is not None
    assert shifted.operator in {"INT_SRIGHT", "INT_RIGHT"}
    assert multiplied is not None
    assert multiplied.operator in {"INT_SRIGHT", "INT_RIGHT"}


def test_parse_wrapper_expr_accepts_cast_heavy_shifted_arithmetic():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_2", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]

    expr = analyzer._parse_wrapper_expr(
        "param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1",
        parameters,
        fallback_index=0,
        local_bindings={},
    )

    assert expr is not None
    rendered = expr.to_string()
    assert "param_2" in rendered
    assert ">> 1" in rendered or "s>> 1" in rendered


def test_structured_reduction_recovery_handles_declared_fragment_concat_assignments():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  undefined4 in_a0_hi;
  long lVar4;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar1 = param_2;
  }
  else {
    iVar1 = 0;
  }
  return iVar1;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert len(recovered) == 2


def test_structured_reduction_recovery_joins_multiline_concat_assignments():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  undefined8 uVar8;
  int iVar2;
  if (param_1 < 1) {
    return 0;
  }
  iVar2 = param_2;
  uVar8 = CONCAT44(iVar2 + iVar2,
                   iVar2 + 1);
  return (int)uVar8;
}
""".strip()

    normalized = analyzer._normalize_wrapper_c_lines(c_text)
    assert "uVar8 = CONCAT44(iVar2 + iVar2, iVar2 + 1);" in normalized

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert _select_return_value(recovered, {"param_1": 0, "param_2": 7}) == 0
    assert _select_return_value(recovered, {"param_1": 3, "param_2": 7}) == 8


def test_structured_reduction_parses_constant_stride_steps():
    analyzer = _make_analyzer()

    assert analyzer._structured_reduction_parse_unit_step("uVar3 = uVar3 - 8", "uVar3") == -8
    assert analyzer._structured_reduction_parse_unit_step("uVar3 -= 8", "uVar3") == -8
    assert analyzer._structured_reduction_parse_unit_step("uVar3 = uVar3 + 8", "uVar3") == 8


def test_structured_reduction_recovery_handles_power_of_two_stride_countdown_loop():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "uint", "size": 4, "is_signed": False},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(uint param_1,int param_2)
{
  uint uVar3;
  int iVar1;
  if (param_1 < 8) {
    return 0;
  }
  uVar3 = param_1 & 0xfffffff8;
  iVar1 = 0;
  do {
    iVar1 = iVar1 + param_2;
    uVar3 = uVar3 - 8;
  } while (uVar3 != 0);
  return iVar1;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for rows in [0, 7, 8, 9, 16, 24]:
        env = {"param_1": rows, "param_2": 3}
        expected = ((rows & 0xFFFFFFF8) // 8) * 3 if rows >= 8 else 0
        assert _select_return_value_wrapped32(recovered, env) == (expected & 0xFFFFFFFF)


def test_structured_do_while_alias_loop_condition_uses_negative_step_hint():
    analyzer = _make_analyzer()
    current_counter = Expression.variable("uVar3", size=4)
    alias_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.variable("uVar3", size=4),
        Expression.constant(0, 4),
    )

    reparsed = analyzer._derive_structured_do_while_alias_loop_condition(
        "uVar3",
        current_counter,
        alias_expr,
        counter_step_hint=-8,
    )

    assert reparsed is not None
    limit_expr, positive_cond = reparsed
    assert limit_expr.to_string() == "0"
    assert positive_cond.to_string() == "(0 < uVar3)"


def test_structured_reduction_recovery_handles_concat_guarded_countdown_loop_from_log():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for rows in range(-1, 6):
        for cols in range(-1, 6):
            env = {
                "param_1": rows,
                "param_2": cols,
                "in_a0_hi": 0,
                "in_a1_hi": 0,
            }
            assert _select_return_value(recovered, env) == _expected_nested_multiply_accumulate(rows, cols)


def test_refine_wrapper_state_conditions_prunes_directly_conflicting_branch_conditions():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_2", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    existing_conditions = [
        Condition(
            Expression.binary_op(
                "INT_SLESS",
                Expression.binary_op(
                    "PIECE",
                    Expression.variable("in_a1_hi", size=4),
                    Expression.parameter("param_2", 0, "int", 4),
                ),
                Expression.constant(1, 8),
            ),
            False,
        )
    ]

    ok, refined = analyzer._refine_wrapper_state_conditions(
        existing_conditions,
        "CONCAT44(in_a1_hi,param_2) < 1",
        parameters,
        {"in_a1_hi": Expression.variable("in_a1_hi", data_type="undefined4", size=4)},
        negated=True,
    )

    assert ok is True
    assert refined is None


def test_evaluate_return_summary_under_environment_derives_fragment_bindings_from_parameters():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    wide_param = Expression.binary_op(
        "PIECE",
        Expression.variable("in_a0_hi", size=4),
        Expression.parameter("param_1", 0, "int", 4),
    )
    wide_param.size = 8
    returns = [
        ReturnInfo(
            address="0x1000",
            value=Expression.constant(0, 4),
            conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESSEQUAL",
                        wide_param,
                        Expression.constant(0, 8),
                    ),
                    False,
                )
            ],
        ),
        ReturnInfo(
            address="0x1000",
            value=Expression.constant(7, 4),
            conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression.constant(0, 8),
                        wide_param,
                    ),
                    False,
                )
            ],
        ),
    ]

    assert analyzer._evaluate_return_summary_under_environment(returns, {"param_1": -1}) == 0x0
    assert analyzer._evaluate_return_summary_under_environment(returns, {"param_1": 3}) == 7


def test_validate_counted_reduction_recovery_accepts_fragment_backed_summaries():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()
    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    analysis = FunctionReturnAnalysis(
        function_name="lr_nested_multiply_accumulate",
        entry_point="0x1000",
        parameters=parameters,
        returns=recovered,
        return_type="int",
    )

    assert analyzer._validate_counted_scalar_reduction_recovery(analysis, recovered) is True


def test_validate_counted_reduction_recovery_accepts_fragment_backed_partial_overlap():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()
    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    partial_analysis = FunctionReturnAnalysis(
        function_name="lr_nested_multiply_accumulate",
        entry_point="0x1000",
        parameters=parameters,
        returns=[
            ret
            for ret in recovered
            if len(ret.conditions) <= 2
            or any("(not ((((in_a0_hi << 32) | param_1) - 1) != 0))" == cond.to_string() for cond in ret.conditions)
        ],
        return_type="int",
    )

    assert len(partial_analysis.returns) < len(recovered)
    assert analyzer._analysis_has_suspicious_peeled_loop_cases(partial_analysis) is True
    assert analyzer._validate_counted_scalar_reduction_recovery(partial_analysis, recovered) is True


def test_validate_counted_reduction_recovery_evaluates_phi_backed_fragment_summary_cases():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()
    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    env = {"param_1": 2, "param_2": 1}
    assert analyzer._evaluate_return_summary_under_environment(recovered, env) == 3
    env = {"param_1": 3, "param_2": 2}
    assert analyzer._evaluate_return_summary_under_environment(recovered, env) == 18


def test_fragment_backed_concat_comparison_prefers_signed_compare():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]

    expr = analyzer._parse_wrapper_expr(
        "CONCAT44(in_a1_hi,param_2) < 1",
        parameters,
        1,
        {"in_a1_hi": Expression.variable("in_a1_hi", data_type="undefined4", size=4)},
    )

    assert expr is not None
    assert expr.operator == "INT_SLESS"


def test_fragment_backed_recovery_uses_signed_concat_guard_for_negative_param_2():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    assert analyzer._evaluate_return_summary_under_environment(
        recovered,
        {"param_1": 1, "param_2": -2},
    ) == 0


def test_parse_wrapper_expr_preserves_widening_casts_before_shift():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_2", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]

    expr = analyzer._parse_wrapper_expr(
        "(int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1)",
        parameters,
        0,
    )

    assert expr is not None
    assert expr.operator == "SUBPIECE"
    widened_shift = expr.operands[0]
    assert widened_shift.operator == "INT_RIGHT"
    assert widened_shift.size == 8
    widened_mult = widened_shift.operands[0]
    assert widened_mult.operator == "INT_MULT"
    assert widened_mult.size == 8
    assert widened_mult.operands[0].operator == "INT_SEXT"
    assert widened_mult.operands[1].operator == "INT_SEXT"


def test_structured_reduction_recovery_preserves_large_ulong_shift_semantics():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    env = {"param_1": 1, "param_2": 0x5E90FE74}
    expected = (env["param_2"] * (env["param_2"] + 1) // 2) & 0xFFFFFFFF
    assert analyzer._evaluate_return_summary_under_environment(recovered, env) == expected


def test_normalize_structured_loop_condition_expr_cancels_shared_additive_terms():
    analyzer = _make_analyzer()
    expr = Expression.binary_op(
        "INT_SLESSEQUAL",
        Expression.binary_op(
            "INT_ADD",
            Expression.constant(1, 4),
            Expression.parameter("param_1", 0, "int", 4),
        ),
        Expression.binary_op(
            "INT_ADD",
            Expression.constant(1, 4),
            Expression.constant(1, 4),
        ),
    )

    normalized = analyzer._normalize_structured_loop_condition_expr(expr)

    assert normalized is not None
    assert normalized.to_string() == "(param_1 <= 1)"


def test_parse_structured_reduction_loop_condition_expr_normalizes_generated_positive_condition():
    analyzer = _make_analyzer()
    parsed = analyzer._parse_structured_reduction_loop_condition_expr(
        counter_name="i",
        start_expr=Expression.binary_op(
            "INT_ADD",
            Expression.parameter("param_1", 0, "int", 4),
            Expression.constant(1, 4),
        ),
        operator="<=",
        left_expr=None,
        right_expr=Expression.binary_op(
            "INT_ADD",
            Expression.constant(1, 4),
            Expression.constant(1, 4),
        ),
        left_is_counter=True,
        right_is_counter=False,
    )

    assert parsed is not None
    assert parsed["positive_cond"].to_string() == "(param_1 <= 1)"


def test_rewrite_structured_reduction_conditions_for_counter_normalizes_shared_additive_terms():
    analyzer = _make_analyzer()
    conditions = [
        Condition(
            Expression.binary_op(
                "INT_SLESSEQUAL",
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(1, 4),
                    Expression.variable("i", size=4),
                ),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.constant(1, 4),
                    Expression.constant(1, 4),
                ),
            ),
            False,
        )
    ]

    rewritten = analyzer._rewrite_structured_reduction_conditions_for_counter(
        conditions,
        counter_name="i",
        nonnegative_vars={"param_1"},
        require_invariant=True,
        counter_replacement=Expression.parameter("param_1", 0, "int", 4),
    )

    assert rewritten is not None
    assert [cond.to_string() for cond in rewritten] == ["(param_1 <= 1)"]


def test_counted_reduction_recovery_normalizes_generated_loop_boundary_conditions():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int lr_nested_multiply_accumulate(int param_1,int param_2)
{
  int iVar1;
  int iVar2;
  int iVar3;
  undefined4 in_a0_hi;
  long lVar4;
  undefined4 in_a1_hi;
  int iVar5;
  lVar4 = CONCAT44(in_a0_hi,param_1);
  if (0 < lVar4) {
    iVar2 = 0;
    iVar3 = param_2 * 2 + (int)((ulong)(param_2 - 1) * (ulong)(param_2 - 2) >> 1) + -1;
    iVar5 = iVar3;
    do {
      iVar1 = iVar5 + iVar3;
      if (CONCAT44(in_a1_hi,param_2) < 1) {
        iVar5 = 0;
      }
      iVar2 = iVar2 + iVar5;
      lVar4 = (long)((int)lVar4 + -1);
      iVar5 = iVar1;
    } while (lVar4 != 0);
    return iVar2;
  }
  return 0;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    all_conditions = [
        cond.to_string()
        for ret in recovered
        for cond in ret.conditions
    ]
    assert "((param_1 + 1) <= (1 + 1))" not in all_conditions
    assert "(param_1 <= 1)" in all_conditions or any(
        "0 == int(" in cond and "param_1" in cond
        for cond in all_conditions
    )


def test_counted_reduction_recovery_only_runs_for_incomplete_summaries():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "rows", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "cols", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    complete_analysis = FunctionReturnAnalysis(
        function_name="lr_nested_multiply_accumulate",
        entry_point="0x1000",
        parameters=parameters,
        returns=[
            ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[
                Condition(Expression.binary_op("INT_SLESSEQUAL", Expression.parameter("rows", 0, "int", 4), Expression.constant(0, 4)), False),
            ]),
            ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[
                Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), Expression.parameter("rows", 0, "int", 4)), False),
                Condition(Expression.binary_op("INT_SLESSEQUAL", Expression.parameter("cols", 1, "int", 4), Expression.constant(0, 4)), False),
            ]),
            ReturnInfo(address="0x1000", value=Expression.parameter("rows", 0, "int", 4), conditions=[
                Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), Expression.parameter("rows", 0, "int", 4)), False),
                Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), Expression.parameter("cols", 1, "int", 4)), False),
            ]),
        ],
        return_type="int",
    )
    assert analyzer._should_attempt_counted_scalar_reduction_recovery(complete_analysis) is False

    incomplete_analysis = FunctionReturnAnalysis(
        function_name="lr_nested_multiply_accumulate",
        entry_point="0x1000",
        parameters=parameters,
        returns=[
            ReturnInfo(address="0x1000", value=Expression.unknown("INT_ADD_budget_exceeded"), conditions=[])
            for _ in range(10)
        ],
        return_type="int",
    )
    assert analyzer._should_attempt_counted_scalar_reduction_recovery(incomplete_analysis) is True


def test_counted_reduction_recovery_runs_for_peeled_loop_case_summaries():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "long", "size": 8, "is_signed": True},
    ]
    peeled_analysis = FunctionReturnAnalysis(
        function_name="lr_nested_multiply_accumulate",
        entry_point="0x1000",
        parameters=parameters,
        returns=[
            ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression.constant(0, 4),
                        Expression.parameter("param_1", 0, "int", 4),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression.parameter("param_2", 1, "long", 8),
                        Expression.constant(1, 8),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.binary_op(
                            "INT_ADD",
                            Expression.parameter("param_1", 0, "int", 4),
                            Expression.constant(4294967295, 4),
                        ),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
            ]),
        ],
        return_type="int",
    )
    c_text = """
int lr_nested_multiply_accumulate(int param_1, long param_2) {
    int acc = 0;
    for (int i = 0; i < param_1; i++) {
        for (int j = 0; j < param_2; j++) {
            acc += (i + 1) * (j + 1);
        }
    }
    return acc;
}
""".strip()

    assert analyzer._should_attempt_counted_scalar_reduction_recovery(peeled_analysis, c_text) is True


def test_counted_reduction_recovery_runs_for_structured_closed_form_after_loop_optimization():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "long", "size": 8, "is_signed": True},
    ]
    peeled_analysis = FunctionReturnAnalysis(
        function_name="lr_nested_multiply_accumulate",
        entry_point="0x1000",
        parameters=parameters,
        returns=[
            ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESSEQUAL",
                        Expression.parameter("param_1", 0, "int", 4),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
            ]),
            ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression.constant(0, 4),
                        Expression.parameter("param_1", 0, "int", 4),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression.parameter("param_2", 1, "long", 8),
                        Expression.constant(1, 8),
                    ),
                    False,
                ),
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression.binary_op(
                            "INT_ADD",
                            Expression.parameter("param_1", 0, "int", 4),
                            Expression.constant(4294967295, 4),
                        ),
                        Expression.constant(0, 4),
                    ),
                    False,
                ),
            ]),
        ],
        return_type="int",
    )
    c_text = """
int lr_nested_multiply_accumulate(int param_1, long param_2) {
    int iVar1;
    if (param_1 < 1) {
        iVar1 = 0;
    } else if (param_2 < 1) {
        iVar1 = 0;
    } else {
        iVar1 = (((param_1 * (param_1 + 1)) / 2) * (((int)param_2 * ((int)param_2 + 1)) / 2));
    }
    return iVar1;
}
""".strip()

    assert analyzer._should_attempt_counted_scalar_reduction_recovery(peeled_analysis, c_text) is True
    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")
    assert recovered is not None


def test_prune_less_precise_return_infos_keeps_unresolved_when_precise_values_conflict():
    analyzer = _make_analyzer()
    condition = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("n", 0, "int", 4),
            Expression.constant(1, 4),
        ),
        False,
    )
    grouped = [
        ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[condition], branch_index=0),
        ReturnInfo(address="0x1000", value=Expression.constant(1, 4), conditions=[condition], branch_index=1),
        ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[condition], branch_index=2),
    ]

    pruned = analyzer._prune_less_precise_return_infos(grouped)

    assert len(pruned) == 3
    assert any(ret.value.expr_type.name == "UNKNOWN" for ret in pruned)
    analysis = FunctionReturnAnalysis(
        function_name="ambiguous_same_region",
        entry_point="0x1000",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=pruned,
        return_type="int",
    )
    assert analyzer._should_attempt_counted_scalar_reduction_recovery(analysis) is True


def test_prune_less_precise_return_infos_drops_unresolved_when_precise_values_agree():
    analyzer = _make_analyzer()
    condition = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("n", 0, "int", 4),
            Expression.constant(1, 4),
        ),
        False,
    )
    grouped = [
        ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[condition], branch_index=0),
        ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=[condition], branch_index=1),
        ReturnInfo(address="0x1000", value=Expression.unknown("phi_circular"), conditions=[condition], branch_index=2),
    ]

    pruned = analyzer._prune_less_precise_return_infos(grouped)

    assert len(pruned) == 2
    assert all(ret.value.expr_type.name != "UNKNOWN" for ret in pruned)


def test_pruning_signature_distinguishes_complementary_condition_regions():
    analyzer = _make_analyzer()
    positive = [Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), Expression.parameter("n", 0, "int", 4)), False)]
    nonpositive = [Condition(Expression.binary_op("INT_SLESSEQUAL", Expression.parameter("n", 0, "int", 4), Expression.constant(0, 4)), False)]

    assert analyzer._pruning_conditions_signature(positive) != analyzer._pruning_conditions_signature(nonpositive)

    analysis = FunctionReturnAnalysis(
        function_name="sign_partition",
        entry_point="0x1000",
        parameters=[{"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True}],
        returns=[
            ReturnInfo(address="0x1000", value=Expression.constant(0, 4), conditions=nonpositive, branch_index=0),
            ReturnInfo(address="0x1000", value=Expression.parameter("n", 0, "int", 4), conditions=positive, branch_index=1),
        ],
        return_type="int",
    )

    assert analyzer._analysis_has_ambiguous_condition_region_returns(analysis) is False
    assert analyzer._should_attempt_counted_scalar_reduction_recovery(analysis) is False


def test_structured_reduction_recovery_recovers_unit_decrement_loop_direction():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int descending_sum(int n) {
    int acc = 0;
    for (int i = n; i > 0; i--) {
        acc += i;
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is not None
    for n in range(-1, 7):
        assert _select_return_value(recovered, {"n": n}) == sum(range(max(n, 0) + 1))


def test_structured_reduction_recovery_rejects_non_unit_loop_step():
    analyzer = _make_analyzer()
    parameters = [
        {"name": "n", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
    ]
    analyzer._current_parameters = parameters
    c_text = """
int descending_sum_stride_two(int n) {
    int acc = 0;
    for (int i = n; i > 0; i -= 2) {
        acc += i;
    }
    return acc;
}
""".strip()

    recovered = analyzer._parse_counted_reduction_from_c_text(c_text, parameters, "0x1000")

    assert recovered is None
