# -*- coding: utf-8 -*-
"""Solver-proven rewrite fallback for pairwise queries."""

from __future__ import annotations

import hashlib
from typing import Any, Dict, Optional, Tuple

from scripts.function_tracer_pcode.proof.formula.input_correspondence.gate import certify_owner_free_identity
from scripts.function_tracer_pcode.core import Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import render_expression_smt_evidence
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.core.live_values import UndecidableComparison
from scripts.function_tracer_pcode.core.structural import value_identity
from scripts.function_tracer_pcode.proof.obligations.pair_disposition import pair_identity_subject
from scripts.function_tracer_pcode.proof.obligations import (
    SolverQueryExecutionReceipt,
    issue_structural_equality_receipt,
    register_structural_equality_producer,
)
from scripts.function_tracer_pcode.proof.formula.returns import coerce_value_to_bitvec_width
from scripts.function_tracer_pcode.semantics.normalize import (
    NormalizationContext,
    NormalizationSettings,
    are_structurally_equivalent,
    normalize_expression,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import build_pair_query


def try_solver_proven_rewrite_equivalence(
    strategy,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> QueryResult:
    settings = getattr(strategy, "solver_proven_rewrite_settings", None)
    if settings is None:
        settings = NormalizationSettings.safe()

    rewritten_expr1 = _build_rewrite_candidate(case1.value_expr, settings)
    rewritten_expr2 = _build_rewrite_candidate(case2.value_expr, settings)

    # 「書き換えが描画を変えたか」（変えていなければ元の式を使う: どの判定でも安全側）。描画の文字列で
    # 比べる: 値の identity は可換の並びを正規化するので、並べ替えただけの書き換えを「変えていない」とする
    changed1 = _exact_expr_key(rewritten_expr1) != _exact_expr_key(case1.value_expr)
    changed2 = _exact_expr_key(rewritten_expr2) != _exact_expr_key(case2.value_expr)
    supporting_solver_receipts = []
    if not changed1 and not changed2:
        result = QueryResult(is_equivalent=None)
        result.pair_stage = "rewrite-no-change"
        result.blocking_reason = "solver_proven_rewrite_no_change"
        result.blocking_detail = "solver-proven rewrite produced no candidate rewrite"
        result.evidence_kind = "pre_normalized_query"
        target_builder = getattr(strategy, "_solver_rewrite_candidate_object_target_key", None)
        if callable(target_builder):
            result.object_target_key = target_builder(
                base_ctx=base_ctx,
                case1=case1,
                case2=case2,
                pair_id=pair_id,
            )
        return result

    if changed1:
        rewrite_receipt = _prove_rewrite(
            strategy,
            base_ctx,
            case1,
            param_replace_fn1,
            rewritten_expr1,
            pair_id,
            label="rewrite-proof-1",
        )
        if rewrite_receipt is None:
            result = QueryResult(is_equivalent=None)
            result.pair_stage = "rewrite-proof-1"
            result.blocking_reason = "solver_proven_rewrite_proof_failed"
            result.blocking_detail = "left rewrite candidate could not be proven equivalent"
            target_builder = getattr(strategy, "_solver_rewrite_proof_object_target_key", None)
            if callable(target_builder):
                result.object_target_key = target_builder(
                    base_ctx=base_ctx,
                    case1=case1,
                    case2=case2,
                    pair_id=pair_id,
                    rewrite_side="left",
                    original_expr=case1.value_expr,
                    rewritten_expr=rewritten_expr1,
                    rewrite_label="rewrite-proof-1",
                )
            return result
        supporting_solver_receipts.append(rewrite_receipt)
    else:
        rewritten_expr1 = case1.value_expr

    if changed2:
        rewrite_receipt = _prove_rewrite(
            strategy,
            base_ctx,
            case2,
            param_replace_fn2,
            rewritten_expr2,
            pair_id,
            label="rewrite-proof-2",
        )
        if rewrite_receipt is None:
            result = QueryResult(is_equivalent=None)
            result.pair_stage = "rewrite-proof-2"
            result.blocking_reason = "solver_proven_rewrite_proof_failed"
            result.blocking_detail = "right rewrite candidate could not be proven equivalent"
            target_builder = getattr(strategy, "_solver_rewrite_proof_object_target_key", None)
            if callable(target_builder):
                result.object_target_key = target_builder(
                    base_ctx=base_ctx,
                    case1=case1,
                    case2=case2,
                    pair_id=pair_id,
                    rewrite_side="right",
                    original_expr=case2.value_expr,
                    rewritten_expr=rewritten_expr2,
                    rewrite_label="rewrite-proof-2",
                )
            return result
        supporting_solver_receipts.append(rewrite_receipt)
    else:
        rewritten_expr2 = case2.value_expr

    rewritten_case1 = _clone_case_with_value_expr(case1, rewritten_expr1)
    rewritten_case2 = _clone_case_with_value_expr(case2, rewritten_expr2)
    # 自明な一致は左右の値を名前（``are_structurally_equivalent``）・runtime ref の key で同一視する。
    # relation が位置どおり・全幅の等式で読みが全幅のときだけ使い、その証明書を receipt に封印する。
    # 通らなければ下の SMT の不等式 query で確かめる（plan v4 PR-P）。
    checked = ((rewritten_case1,), (rewritten_case2,))
    certification = certify_owner_free_identity(*checked, subject=pair_identity_subject(pair_id))
    if certification.passed and _rewritten_values_are_trivially_equal(
        strategy,
        base_ctx,
        rewritten_case1,
        rewritten_case2,
    ):
        required_projection_bindings = tuple(
            (base_ctx.get("call_projection_binding_ids_by_pair") or {}).get(
                pair_id, ()
            )
            or ()
        )
        if required_projection_bindings:
            rewritten_query = build_pair_query(
                base_ctx,
                rewritten_case1,
                rewritten_case2,
                param_replace_fn1,
                param_replace_fn2,
                pair_id,
            )
            result = strategy._solve_query_internal(
                rewritten_query,
                pair_id,
                stage="rewrite-structural-projection",
                use_hard_timeout=True,
            )
            result.last_query = rewritten_query
            result.pair_stage = "rewrite-structural-projection"
            execution_receipt = getattr(
                result, "solver_query_execution_receipt", None
            )
            if result.is_equivalent is not True:
                return result
            if (
                type(execution_receipt) is not SolverQueryExecutionReceipt
                or not execution_receipt.validates_execution(
                    query=rewritten_query,
                    expected_disposition="unsat",
                    expected_query_label=pair_id,
                )
            ):
                result.is_equivalent = None
                result.blocking_reason = "structural_projection_query_authority_missing"
                result.blocking_detail = (
                    "structural rewrite with call projection lacks an exact "
                    "UNSAT execution receipt"
                )
                return result
            supporting_solver_receipts.append(execution_receipt)
        else:
            result = QueryResult(is_equivalent=True)
            result.pair_stage = "rewrite-structural"
        result.structural_equality_receipt = (
            issue_structural_equality_receipt(
                query_label=pair_id,
                proof_kind="rewrite-structural",
                evidence=(
                    "rewrite-structural",
                    value_identity(rewritten_expr1),
                    value_identity(rewritten_expr2),
                    int(base_ctx.get("return_size1", 0) or 0),
                    int(base_ctx.get("return_size2", 0) or 0),
                    bool(rewritten_case1.should_sign_extend_value()),
                    bool(rewritten_case2.should_sign_extend_value()),
                ),
                supporting_solver_receipts=tuple(
                    supporting_solver_receipts
                ),
                identity_certificate=certification.certificate,
                checked_values=checked,
            )
        )
        return result

    rewritten_query = build_pair_query(
        base_ctx,
        rewritten_case1,
        rewritten_case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    result = strategy._solve_query_internal(
        rewritten_query,
        pair_id,
        stage="rewrite-ineq",
        use_hard_timeout=True,
    )
    result.last_query = rewritten_query
    result.pair_stage = "rewrite-ineq"
    return result


def _rewritten_values_are_trivially_equal(
    strategy,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
) -> bool:
    if base_ctx.get("return_size1", 32) != base_ctx.get("return_size2", 32):
        return False
    if case1.should_sign_extend_value() != case2.should_sign_extend_value() and not _sign_extension_irrelevant(
        base_ctx,
        case1.value_expr,
        case2.value_expr,
    ):
        return False

    left = case1.value_expr
    right = case2.value_expr
    if _intrinsic_values_match(strategy, case1, case2):
        return True

    equivalent, _reason = are_structurally_equivalent(
        left,
        right,
        debug=bool(getattr(strategy, "debug", False)),
    )
    if not equivalent:
        return False
    return _expression_sizes_compatible(left, right)


def _sign_extension_irrelevant(
    base_ctx: Dict[str, Any],
    left: Expression,
    right: Expression,
) -> bool:
    target_bits = int(base_ctx.get("return_size1", 32) or 32)
    left_bits = _expr_known_bits(left)
    right_bits = _expr_known_bits(right)
    return left_bits is not None and right_bits is not None and left_bits >= target_bits and right_bits >= target_bits


def _expr_known_bits(expr: Expression) -> Optional[int]:
    size = int(getattr(expr, "size", 0) or 0)
    if size <= 0:
        return None
    return size * 8


def _intrinsic_values_match(strategy, case1: ReturnCase, case2: ReturnCase) -> bool:
    intrinsic_equivalent = getattr(strategy, "_intrinsic_runtime_values_equivalent", None)
    if not callable(intrinsic_equivalent):
        return False
    try:
        return bool(
            intrinsic_equivalent(
                case1.value_expr,
                case2.value_expr,
                left_case=case1,
                right_case=case2,
            )
        )
    except UndecidableComparison:
        # 組み込みの code だけでは比べられない値（Issue #242）: 引数を減らして比べ直さない（判定不能を一致の根拠にしない）
        return False
    except TypeError:
        return bool(intrinsic_equivalent(case1.value_expr, case2.value_expr))


def _expression_sizes_compatible(left: Expression, right: Expression) -> bool:
    left_size = int(getattr(left, "size", 0) or 0)
    right_size = int(getattr(right, "size", 0) or 0)
    if left_size > 0 and right_size > 0 and left_size != right_size:
        return False

    left_operands = list(getattr(left, "operands", []) or [])
    right_operands = list(getattr(right, "operands", []) or [])
    if len(left_operands) != len(right_operands):
        return False
    return all(
        _expression_sizes_compatible(left_operand, right_operand)
        for left_operand, right_operand in zip(left_operands, right_operands)
    )


def _clone_case_with_value_expr(case: ReturnCase, value_expr: Expression) -> ReturnCase:
    return ReturnCase(
        index=case.index,
        conditions=list(case.conditions),
        value_expr=value_expr,
        return_info=case.return_info,
        normalized_value_expr=value_expr,
        return_type=case.return_type,
        return_type_obj=case.return_type_obj,
        source_indices=list(case.source_indices),
        parameters=list(case.parameters),
        effect_summary=case.effect_summary,
        comparison_surface=case.comparison_surface,
        summary_conditions=list(case.summary_conditions),
    )


def _build_rewrite_candidate(expr: Expression, settings: NormalizationSettings) -> Expression:
    """書き換え候補を 1 本組み立てる。**この関数の出口が公開点**。

    候補はここで完成し、以後は鍵にされ・照合され・solver へ渡されるだけなので、
    確定した意味として公開してから返す。
    """

    pre_rewritten = _apply_solver_proven_candidate_rewrites(expr, _ConstructionOrder())
    normalized = normalize_expression(
        pre_rewritten,
        NormalizationContext(settings=settings),
    )
    return publish(_apply_solver_proven_candidate_rewrites(normalized, _ConstructionOrder()))


def _apply_solver_proven_candidate_rewrites(
    expr: Expression,
    order: Optional["_ConstructionOrder"] = None,
) -> Expression:
    order = order if order is not None else _ConstructionOrder()
    expr_type = getattr(expr, "expr_type", None)
    if expr_type != ExpressionType.BINARY_OP:
        return expr

    operands = list(getattr(expr, "operands", []) or [])
    if len(operands) != 2:
        return expr

    left = _apply_solver_proven_candidate_rewrites(operands[0], order)
    right = _apply_solver_proven_candidate_rewrites(operands[1], order)
    operator = getattr(expr, "operator", None)

    rewritten = _maybe_rewrite_modulo_expansion(expr, operator, left, right)
    if rewritten is not None:
        return rewritten

    if operator in {
        "INT_ADD",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "INT_EQUAL",
        "INT_NOTEQUAL",
    }:
        ordered = order.commutative_operands(left, right)
        if ordered[0] is not left or ordered[1] is not right:
            return Expression(
                ExpressionType.BINARY_OP,
                operator=operator,
                operands=ordered,
                size=getattr(expr, "size", None),
            )

    if left is operands[0] and right is operands[1]:
        return expr

    return Expression(
        ExpressionType.BINARY_OP,
        operator=operator,
        operands=[left, right],
        size=getattr(expr, "size", None),
    )


def _maybe_rewrite_modulo_expansion(
    original_expr: Expression,
    operator: Optional[str],
    left: Expression,
    right: Expression,
) -> Optional[Expression]:
    if operator != "INT_SUB":
        return None

    multiplicands = _extract_binary_operands(right, "INT_MULT")
    if multiplicands is None:
        return None

    dividend = None
    divisor = None
    remainder_operator = None
    for candidate_div, candidate_other in (
        multiplicands,
        (multiplicands[1], multiplicands[0]),
    ):
        div_operands = _extract_binary_operands(candidate_div, "INT_SDIV")
        if div_operands is not None:
            dividend, divisor = div_operands
            remainder_operator = "INT_SREM"
            if _exprs_match(left, dividend) and _exprs_match(candidate_other, divisor):
                break
        div_operands = _extract_binary_operands(candidate_div, "INT_DIV")
        if div_operands is not None:
            dividend, divisor = div_operands
            remainder_operator = "INT_REM"
            if _exprs_match(left, dividend) and _exprs_match(candidate_other, divisor):
                break
    else:
        return None

    return Expression(
        ExpressionType.BINARY_OP,
        operator=remainder_operator,
        operands=[left, divisor],
        size=getattr(original_expr, "size", None),
    )


def _extract_binary_operands(expr: Expression, operator: str):
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(expr, "operator", None) != operator:
        return None
    operands = list(getattr(expr, "operands", []) or [])
    if len(operands) != 2:
        return None
    return operands[0], operands[1]


def _exprs_match(left: Expression, right: Expression) -> bool:
    # 照合は値の identity（#218 PR-D）。描画した SMT の文字列は PARAMETER の幅などを持たないので、
    # 幅だけ違う 2 つの式を同じとみなす
    return value_identity(left) == value_identity(right)


def _same_operand(left: Expression, right: Expression) -> bool:
    """最小の差分の探索で飛ばしてよい operand の組か: 値も描画も同じ（#218 PR-D）。

    値が同じなら飛ばしても証明は健全で、描画が違う（可換の並べ替え）組は従来どおり差分として辿る。
    描画だけ同じで値の違う組（幅だけ違う PARAMETER）は飛ばさない。
    """

    return _exprs_match(left, right) and _exact_expr_key(left) == _exact_expr_key(right)


def _exact_expr_key(expr: Expression) -> str:
    """描画した文字列（**公開済みの式の、書き換えが描画を変えたかの検出だけ**。一致の判定・identity に使わない）。

    書き換えが描画を変えたら `_prove_rewrite` が元の式との等しさを solver で証明し、変えていなければ元の式を
    使う（どちらに外れても、証明の無い書き換えは使わない）。operand の一致は `_exprs_match`（値の identity）が
    決める（#218 PR-D。名前は broad except の baseline の key なので変えない）。

    入力は公開済みの候補と元の式（とその部分式）だけで、solver へ渡す描画（`to_smt`）とその出力予算の契約を
    そのまま使う: 予算を超えれば限界として台帳に残る（その候補は solver へも渡せない）。組み立て途中の
    未公開の node を並べる鍵は `_ConstructionOrder`（Issue #281）。
    """

    try:
        return expr.to_smt(float_mode="fp")
    except Exception:
        structural_key = getattr(expr, "structural_key", None)
        if callable(structural_key):
            return repr(structural_key(budget=256))
        return repr(expr)


#: 描画を鍵にする部分木の大きさの上限（木の節点数）。これより大きい部分木は子の鍵から合成した digest を鍵にする
_RENDERED_ORDER_KEY_MAX_NODES = 64


class _ConstructionOrder:
    """候補を組み立てている途中で、可換演算の 2 項を並べる順（Issue #281）。1 回の組み立てごとに作る。

    並べる対象は `_apply_solver_proven_candidate_rewrites` が作り直した **未公開** の node を含むので、
    公開を要求する `to_smt` は使えない（未公開の入力として内部バグになる。V281 で観測）。

    鍵（全順序・process をまたいで決定的。等しい値の部分木は両側で同じ鍵になる）:

    * 木の節点数が `_RENDERED_ORDER_KEY_MAX_NODES` 以下の部分木: `(0, 証拠用の描画)`。公開済みの入力では
      `to_smt` と同じ文字列なので、典型的な大きさの式の並べる順は solver の描画の順のまま。
    * それより大きい部分木: `(1, digest)`。digest は node の種類・演算子・名前・幅・opcode と子の鍵から
      合成する（子の鍵は memo するので、各 node の鍵は 1 回だけ作る）。

    描画の鍵だけにすると、各可換 node が部分木を描画し直すので、組み立ての費用は部分木の大きさの和
    （深い鎖で節点数の 2 乗）になる（PR #283 の計測: 葉 200 の木で 1.2 秒、費用の 85% が鍵）。上の鍵は、
    描画する部分木の大きさが上限で抑えられるので、費用は節点数 × 上限で抑えられる。

    出力予算（`render_bytes`）はここへ当てない: 予算の owner は solver へ渡す描画だけで、それ以外へ渡すことは
    禁じている（`test_architecture_boundaries` の 2 つの契約）。描画するのは上限以下の部分木だけ。予算は、
    並べた候補を solver の描画へ通すところで掛かる（変化の検出の `_exact_expr_key` と `_prove_rewrite`）。

    並べる順は候補の形だけを決め、正しさは決めない: 書き換えが描画を変えた候補は `_prove_rewrite` が
    元の式との等しさを solver で証明する。
    """

    def __init__(self) -> None:
        # memo は node を値に持ち、組み立ての間 node を生かしておく（解放された node の id を別の node が
        # 再利用すると、古い鍵を引いてしまう）
        self._sizes: Dict[int, Tuple[Expression, int]] = {}
        self._keys: Dict[int, Tuple[Expression, Tuple[int, str]]] = {}

    def commutative_operands(self, left: Expression, right: Expression) -> list:
        """可換演算の 2 項を鍵の順に並べる（`sorted` と同じ安定な順: 等しければ元の順）。"""

        return [right, left] if self.key(right) < self.key(left) else [left, right]

    def key(self, expr: Expression) -> Tuple[int, str]:
        cached = self._keys.get(id(expr))
        if cached is not None:
            return cached[1]
        if self._tree_size(expr) <= _RENDERED_ORDER_KEY_MAX_NODES:
            result = (0, render_expression_smt_evidence(expr, float_mode="fp"))
        else:
            result = (1, self._digest(expr))
        self._keys[id(expr)] = (expr, result)
        return result

    def _children(self, expr: Expression) -> list:
        if expr.expr_type == ExpressionType.PHI and expr.value:
            children = []
            for cond, value in expr.value:
                if cond is not None:
                    children.append(cond.expression)
                children.append(value)
            return children
        return list(getattr(expr, "operands", None) or ())

    def _tree_size(self, expr: Expression) -> int:
        """木の節点数（上限 + 1 で打ち切る。共有された部分木は出現ごとに数える）。"""

        cached = self._sizes.get(id(expr))
        if cached is not None:
            return cached[1]
        total = 1
        for child in self._children(expr):
            total += self._tree_size(child)
            if total > _RENDERED_ORDER_KEY_MAX_NODES:
                total = _RENDERED_ORDER_KEY_MAX_NODES + 1
                break
        self._sizes[id(expr)] = (expr, total)
        return total

    def _digest(self, expr: Expression) -> str:
        digest = hashlib.sha256()
        negations = []
        if expr.expr_type == ExpressionType.PHI and expr.value:
            negations = [None if cond is None else bool(cond.negated) for cond, _value in expr.value]
        head = (
            expr.expr_type.name,
            getattr(expr, "operator", None),
            getattr(expr, "name", None),
            getattr(expr, "size", None),
            getattr(expr, "opcode", None),
            negations,
        )
        digest.update(repr(head).encode("utf-8"))
        for child in self._children(expr):
            kind, text = self.key(child)
            digest.update(b"\x00%d\x00" % kind)
            digest.update(text.encode("utf-8"))
        return digest.hexdigest()


def _prove_rewrite(
    strategy,
    base_ctx: Dict[str, Any],
    case: ReturnCase,
    param_replace_fn,
    rewritten_expr: Expression,
    pair_id: str,
    *,
    label: str,
) -> Optional[SolverQueryExecutionReceipt]:
    query = _build_rewrite_proof_query(
        base_ctx,
        case,
        param_replace_fn,
        rewritten_expr,
        label,
    )
    result = strategy._solve_query_internal(
        query,
        pair_id,
        stage=label,
        use_hard_timeout=False,
    )
    receipt = getattr(result, "solver_query_execution_receipt", None)
    if (
        result.is_equivalent is True
        and type(receipt) is SolverQueryExecutionReceipt
        and receipt.validates_execution(
            query=query,
            expected_disposition="unsat",
            expected_query_label=pair_id,
            expected_model=None,
        )
    ):
        return receipt
    return None


def _build_rewrite_proof_query(
    base_ctx: Dict[str, Any],
    case: ReturnCase,
    param_replace_fn,
    rewritten_expr: Expression,
    label: str,
) -> str:
    return_size = base_ctx.get("return_size1", 32)
    if label.endswith("-2"):
        return_size = base_ctx.get("return_size2", return_size)

    original_expr, proof_expr = _extract_minimal_rewrite_difference(
        case.value_expr,
        rewritten_expr,
    )
    proof_target_bits = _proof_target_bits(original_expr, proof_expr, return_size)

    use_sign_extension = False
    original_smt = _render_expression_smt(
        original_expr,
        param_replace_fn,
        proof_target_bits,
        use_sign_extension=use_sign_extension,
    )
    rewritten_smt = _render_expression_smt(
        proof_expr,
        param_replace_fn,
        proof_target_bits,
        use_sign_extension=use_sign_extension,
    )

    lines = [
        "; ============================================================",
        f"; Solver-proven rewrite proof: {label}",
        "; ============================================================",
        "",
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.append("")
    lines.append("; ----------------------------------------")
    lines.append("; Case conditions")
    lines.append("; ----------------------------------------")
    for condition_smt in case.get_conditions_smt(param_replace_fn):
        lines.append(f"(assert {condition_smt})")
    lines.append("")
    lines.append("; ----------------------------------------")
    lines.append("; Rewrite non-equivalence check")
    lines.append("; ----------------------------------------")
    lines.append(f"(assert (not (= {original_smt} {rewritten_smt})))")
    lines.append("")
    lines.append("(check-sat)")
    return "\n".join(lines)


def _extract_minimal_rewrite_difference(
    original_expr: Expression,
    rewritten_expr: Expression,
):
    if _same_operand(original_expr, rewritten_expr):
        return original_expr, rewritten_expr

    if (
        getattr(original_expr, "expr_type", None) != getattr(rewritten_expr, "expr_type", None)
        or getattr(original_expr, "operator", None) != getattr(rewritten_expr, "operator", None)
    ):
        return original_expr, rewritten_expr

    original_operands = list(getattr(original_expr, "operands", []) or [])
    rewritten_operands = list(getattr(rewritten_expr, "operands", []) or [])
    if len(original_operands) != len(rewritten_operands):
        return original_expr, rewritten_expr

    differing_indices = [
        index
        for index, (lhs, rhs) in enumerate(zip(original_operands, rewritten_operands))
        if not _same_operand(lhs, rhs)
    ]
    if len(differing_indices) != 1:
        return original_expr, rewritten_expr

    differing_index = differing_indices[0]
    return _extract_minimal_rewrite_difference(
        original_operands[differing_index],
        rewritten_operands[differing_index],
    )


def _proof_target_bits(
    original_expr: Expression,
    rewritten_expr: Expression,
    fallback_bits: int,
) -> int:
    original_bits = getattr(original_expr, "size", None)
    rewritten_bits = getattr(rewritten_expr, "size", None)
    if isinstance(original_bits, int) and isinstance(rewritten_bits, int):
        return max(original_bits, rewritten_bits) * 8
    if isinstance(original_bits, int):
        return original_bits * 8
    if isinstance(rewritten_bits, int):
        return rewritten_bits * 8
    return fallback_bits


def _render_expression_smt(
    expr: Expression,
    param_replace_fn,
    target_bits: int,
    *,
    use_sign_extension: bool,
) -> str:
    if param_replace_fn is None:
        rendered = expr.to_smt(float_mode="fp")
    else:
        try:
            rendered = param_replace_fn(expr)
        except TypeError:
            rendered = param_replace_fn(expr.to_smt(float_mode="fp"))
    if not isinstance(rendered, str):
        to_smt = getattr(rendered, "to_smt", None)
        rendered = to_smt(float_mode="fp") if callable(to_smt) else str(rendered)
    return coerce_value_to_bitvec_width(
        expr,
        rendered,
        target_bits,
        use_sign_extension=use_sign_extension,
    )


register_structural_equality_producer(
    "rewrite-structural",
    try_solver_proven_rewrite_equivalence,
)
