# -*- coding: utf-8 -*-
"""old / new 描画の意味比較に使う式の corpus（**両方の commit で同じ式**）。

この module は `core/expression.py` / `core/condition.py` / `core/runtime_refs`
しか使わない。PR-22-C が触った描画側には依存しないので、変更前の commit へ
そのまま持っていっても同じ式が組める — baseline を録る側と比べる側で式が
違ったら、比較そのものが無意味になる。

網羅する面は PR-22-C が触った描画の面そのもの: 算術 / 比較 / 幅と符号拡張 /
Bool / PHI と branch 条件 / MEMORY と address 文脈 / float / intrinsic /
loop lowering / unknown 宣言 / 文脈依存の描画。
"""

from __future__ import annotations

from typing import Any, Dict

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs.locations import AddressValueRef
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef


def _param(name: str, index: int, size: int = 4) -> Expression:
    return Expression.parameter(name, index, size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _variable(name: str, size: int = 4, runtime_ref: Any = None) -> Expression:
    return Expression(ExpressionType.VARIABLE, name=name, size=size, runtime_ref=runtime_ref)


def _binary(operator: str, left, right, size: int = 4) -> Expression:
    expr = Expression.binary_op(operator, left, right)
    expr.size = size
    return expr


def _unary(operator: str, operand, size: int = 4) -> Expression:
    expr = Expression.unary_op(operator, operand)
    expr.size = size
    return expr


def _memory(address, size: int = 4) -> Expression:
    return Expression(ExpressionType.MEMORY, operands=[address], size=size)


def _intrinsic(name: str, operands, size: int = 4, opcode=None) -> Expression:
    return Expression(
        ExpressionType.INTRINSIC,
        name=name,
        operands=list(operands),
        size=size,
        opcode=opcode,
    )


def _doubling(depth: int, leaf: Expression) -> Expression:
    # P-code の INT_ADD は出力と入力の大きさが同じ（Issue #298: 宣言が被演算子より広い算術は、
    # 伸ばし方が決まらなければ描画が拒否する）。変更前の描画は葉の幅で計算していたので、
    # 葉の大きさで宣言しても記録した描画（baseline）と同じ意味になる
    node = leaf
    for _ in range(depth):
        node = _binary("INT_ADD", node, node, size=int(leaf.size or 4))
    return node


def _chain(depth: int, leaf: Expression, step: Expression) -> Expression:
    node = leaf
    for _ in range(depth):
        node = _binary("INT_ADD", node, step)
    return node


def build_corpus() -> Dict[str, Dict[str, Any]]:
    """`{case: {"expression": …, "float_mode": …}}`。順序は決定的。"""

    a = _param("a", 0)
    b = _param("b", 1)
    wide = _param("w", 2, size=8)
    narrow = _param("n", 3, size=1)
    byte_value = _param("q", 4, size=1)
    f32 = _param("f", 5, size=4)
    g32 = _param("g", 6, size=4)
    f64 = _param("d", 7, size=8)

    global_ref = AddressValueRef(address_offset=0x2000, source="ghidra_object")
    global_variable = _variable("gvar", size=8, runtime_ref=global_ref)
    # UNKNOWN の symbol 名は runtime identity から作られる。identity が無いと
    # `id()` に落ちて process ごとに名前が変わり、別 process で録った baseline と
    # 比べられない。corpus では安定した identity を与える。
    unknown = Expression(
        ExpressionType.UNKNOWN,
        name="rt_unknown",
        size=4,
        runtime_ref=PcodeOpRef(address_offset=0x1234, seq_time=7, seq_order=3, mnemonic="CALL"),
    )

    shared_sum = _binary("INT_ADD", a, b)
    condition = Condition(_binary("INT_LESS", a, b, size=1))
    negated_condition = Condition(_binary("INT_LESS", a, b, size=1), True)
    expression_condition = _binary("INT_SLESS", a, b, size=1)

    phi_with_condition = Expression.phi(
        [(condition, shared_sum), (None, _binary("INT_MULT", a, a))]
    )
    phi_with_condition.size = 4
    phi_with_expression_condition = Expression.phi(
        [(expression_condition, shared_sum), (None, b)]
    )
    phi_with_expression_condition.size = 4
    phi_bool = Expression.phi(
        [
            (condition, _binary("INT_EQUAL", a, b, size=1)),
            (None, _binary("INT_NOTEQUAL", a, b, size=1)),
        ]
    )
    phi_bool.size = 1

    corpus: Dict[str, Dict[str, Any]] = {
        # --- 算術 / 比較 -------------------------------------------------
        "arith_small": _binary("INT_ADD", a, b),
        "arith_mixed_operators": _binary(
            "INT_XOR",
            _binary("INT_MULT", _binary("INT_SUB", a, b), _const(3)),
            _binary("INT_AND", _binary("INT_OR", a, b), _const(0xFF)),
        ),
        "arith_shifts": _binary(
            "INT_OR",
            _binary("INT_LEFT", _doubling(4, a), _const(3)),
            _binary("INT_SRIGHT", _doubling(4, b), _const(2)),
        ),
        "arith_signed_division": _binary(
            "INT_SDIV", _binary("INT_SREM", _doubling(4, a), b), _const(7)
        ),
        "compare_unsigned": _binary("INT_LESS", _doubling(5, a), _doubling(5, b), size=1),
        "compare_signed": _binary("INT_SLESS", _doubling(5, a), _doubling(5, b), size=1),
        "compare_equality_of_bools": _binary(
            "INT_EQUAL",
            _binary("INT_LESS", a, b, size=1),
            _binary("INT_LESSEQUAL", b, a, size=1),
            size=1,
        ),
        # --- 幅 / 符号拡張 -----------------------------------------------
        "width_sign_extension": _binary(
            "INT_ADD",
            _unary("INT_SEXT", _doubling(4, narrow), size=4),
            _unary("INT_ZEXT", _doubling(4, byte_value), size=4),
        ),
        "width_piece_subpiece": _binary(
            "SUBPIECE",
            _binary("PIECE", _doubling(3, a), _doubling(3, b), size=8),
            _const(2),
            size=4,
        ),
        "width_signed_widening_in_arithmetic": _binary(
            "INT_MULT",
            _unary("INT_SEXT", byte_value, size=4),
            _binary("INT_SDIV", _doubling(4, a), _const(3)),
        ),
        "width_negate_and_twos_complement": _binary(
            "INT_ADD",
            _unary("INT_NEGATE", _doubling(4, a), size=4),
            _unary("INT_2COMP", _doubling(4, b), size=4),
        ),
        # --- Bool ---------------------------------------------------------
        "bool_connectives": _binary(
            "BOOL_OR",
            _binary(
                "BOOL_AND",
                _binary("INT_LESS", _doubling(4, a), b, size=1),
                _binary("INT_NOTEQUAL", _doubling(4, b), a, size=1),
                size=1,
            ),
            _unary("BOOL_NEGATE", _binary("INT_EQUAL", a, b, size=1), size=1),
            size=1,
        ),
        "bool_to_bitvector": _binary(
            "INT_ADD",
            _unary("INT_ZEXT", _binary("INT_LESS", _doubling(4, a), b, size=1), size=4),
            _doubling(4, b),
        ),
        # --- PHI / branch 条件 ----------------------------------------------
        "phi_with_condition": _doubling(4, phi_with_condition),
        "phi_with_expression_condition": _doubling(3, phi_with_expression_condition),
        "phi_bool_branches": phi_bool,
        "phi_negated_condition": Expression.phi(
            [(negated_condition, _doubling(4, a)), (None, _doubling(4, b))]
        ),
        # --- MEMORY / address 文脈 ------------------------------------------
        "memory_read": _binary("INT_ADD", _doubling(4, _memory(wide)), _doubling(4, a)),
        "memory_of_global": _memory(global_variable),
        "context_global_as_address_and_value": _binary(
            "INT_ADD",
            _doubling(4, _memory(global_variable)),
            _doubling(4, _unary("INT_ZEXT", global_variable, size=4)),
        ),
        "memory_width_8": _binary(
            "INT_ADD",
            _unary("INT_ZEXT", _memory(wide, size=1), size=4),
            _doubling(3, a),
        ),
        # --- unknown 宣言 ----------------------------------------------------
        "unknown_symbol": _binary("INT_ADD", _doubling(4, unknown), _doubling(4, a)),
        # --- intrinsic --------------------------------------------------------
        "intrinsic_ptradd": _intrinsic(
            "PTRADD", [_doubling(3, wide), _param("i", 8, size=8), _const(4, size=8)], size=8
        ),
        # --- float ------------------------------------------------------------
        "float_arithmetic_uf": _binary("FLOAT_ADD", _doubling(3, f32), g32),
        "float_predicate_uf": _binary("FLOAT_LESS", _doubling(3, f32), g32, size=1),
        "float_unary_uf": _unary("FLOAT_ABS", _doubling(3, f32), size=4),
    }

    cases: Dict[str, Dict[str, Any]] = {
        name: {"expression": expression, "float_mode": "uf"}
        for name, expression in corpus.items()
    }

    # float 理論を使う描画は別 mode で。`_normalize_to_fp_expr` の分岐はこちら
    # にしか出ないので、old / new の比較で外せない。
    fp_cases = {
        "fp_arithmetic": _binary("FLOAT_ADD", _doubling(3, f32), g32),
        "fp_nested_arithmetic": _binary(
            "FLOAT_MULT", _binary("FLOAT_ADD", f32, g32), _binary("FLOAT_SUB", f32, g32)
        ),
        "fp_predicate": _binary("FLOAT_LESS", _doubling(3, f32), g32, size=1),
        "fp_predicate_over_arithmetic": _binary(
            "FLOAT_EQUAL", _binary("FLOAT_ADD", f32, g32), _binary("FLOAT_MULT", f32, g32), size=1
        ),
        "fp_int_to_float": _unary("INT2FLOAT", _doubling(3, a), size=4),
        "fp_double_width": _binary("FLOAT_DIV", _doubling(2, f64), _param("e", 9, size=8), size=8),
        "fp_mixed_with_integer": _binary(
            "INT_ADD",
            _unary("INT_ZEXT", _binary("FLOAT_LESS", f32, g32, size=1), size=4),
            _doubling(3, a),
        ),
    }
    for name, expression in fp_cases.items():
        cases[name] = {"expression": expression, "float_mode": "fp"}

    # 文脈依存（符号拡張の好み）の描画。root からの文脈が子へ伝わる経路。
    cases["context_prefer_signed_arithmetic"] = {
        "expression": _binary(
            "INT_ADD", _unary("INT_SEXT", byte_value, size=4), _doubling(4, a)
        ),
        "float_mode": "uf",
        "prefer_signed_arithmetic": True,
    }
    cases["context_address"] = {
        "expression": _doubling(3, global_variable),
        "float_mode": "uf",
        "address_context": True,
    }

    # 共有の深い DAG と、線形の深い式（描画の形が最も変わるところ）。
    cases["shared_dag_depth_10"] = {"expression": _doubling(10, a), "float_mode": "uf"}
    cases["linear_depth_200"] = {
        "expression": _chain(200, a, _const(1)),
        "float_mode": "uf",
    }
    return cases
