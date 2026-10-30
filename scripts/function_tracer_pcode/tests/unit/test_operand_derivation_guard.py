# -*- coding: utf-8 -*-
"""operand を差し替えた式を、`derive_with_operands` 以外で作る新しい書き方を禁じる（Issue #281）。

#281 は、node を operand だけ差し替えて作り直す site が field（`opcode`）を落としたことから起きた。
field と runtime ref の扱いの owner は `core/operand_derivation.py`（`Expression.derive_with_operands`）
1 つにする。この test は、owner を通らずに **既存の node の ref・種類を写して operand を差し替える** 書き方を
AST で数える（種類と、それぞれがなぜ危ないか）:

* ``clone_with_operands`` — ``<式>.clone_with(..., operands=...)`` と ``clone_with(**...)``。`clone_with` は
  ref を既定で写すので、新しい operand に古い ref が付く
* ``derive_with_operands`` — ``<式>.derive_with(operands=...)`` と ``derive_with(**...)``。中で `clone_with`
  を呼ぶので上と同じ。`derive_with` は実行時にも `operands` を拒む（下の test。`**` で渡しても止まる）
* ``copied_expr_type_with_operands`` — ``Expression(<式>.expr_type, ..., operands)``（keyword でも位置引数
  でも）。既存の node の種類を写して作り直す（#281 の形）
* ``copied_runtime_ref`` — 上のどれでもない呼び出しが ``runtime_ref=<式>.runtime_ref`` /
  ``runtime_ref=getattr(<式>, "runtime_ref", ...)`` を渡す（``Expression.memory(新しい番地, ..., runtime_ref=
  expr.runtime_ref)`` など factory 経由で ref を新しい operand に付ける）。leaf を写すだけの site も数える
  （呼び出しの形からは operand の有無を決められないので、多めに数えて baseline に入れる）
* ``operands_store`` — 既存の node の ``.operands`` / ``.operands[i]`` への代入、``setattr(_, "operands", _)``、
  ``__dict__["operands"]`` への代入（作った後に operand だけを変える）

既存の site は `BASELINE` に (file, 関数の qualname, 種類) ごとの数で入れてある。**baseline は削るだけ**:

* baseline に無い site・数が増えた site は失敗する（新しい site は `derive_with_operands` を使う）
* site を `derive_with_operands` へ移したら、その行を消す（数が減ったのに baseline が古いままでも失敗する）

正当な用途を妨げないための範囲: operand を変えない複製（``clone_with(size=4)``、``derive_with(size=...)``）と、
factory で一から作る式（ref を写さない）は数えない。ref を明示して作り直す site（`derive_with_operands` が
決めた ref を渡す owner）は `OWNER_SITES` に置く。

**この guard の限界**（AST の形で数えるので、次は見えない。review で確かめる）:

* ref を変数へ取り出してから渡す書き方（``ref = expr.runtime_ref; Expression.memory(a, runtime_ref=ref)``）
* baseline の helper（``switch._clone_expression`` など）を新しい呼び出し側から使うこと（helper の中の
  1 site として数えるだけで、呼び出し側は増えても見えない）
* factory で一から作り直して ref・field を **落とす** 書き方（``Expression.binary_op(expr.operator, ...)``）。
  古い ref は残らないが、post-state の ref を落とすと pre-state の読み出しに化ける（`operand_derivation`
  の docstring）。件数が多く、ref を持たない node の正規化が大半なので数えていない
* `copy.copy` などの汎用の複製（production には無い。走査で確認済み）
"""

import ast
import functools
import os
from collections import Counter

import pytest

PACKAGE_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

#: owner そのもの（ここだけが operand を差し替えた node を作ってよい）と、実行時に operand を拒む入口
OWNER_SITES = frozenset({
    ("core/operand_derivation.py", "derive_with_operands", "copied_expr_type_with_operands"),
    # `derive_with(**fields)` は `operands` を実行時に拒んでから `clone_with` へ渡す
    ("core/expression.py", "Expression.derive_with", "clone_with_operands"),
})

#: 既存の site（Issue #281 の時点）。削るだけ。移した site の行は消す
BASELINE = {
    ("analysis/condition/simplifier.py", "ConditionSimplifier._reduce_expression_under_conditions", "copied_expr_type_with_operands"): 1,
    ("analysis/condition/smt_oracle.py", "ConditionSMTOracle._rewrite_expr_with_symbol_names", "clone_with_operands"): 1,
    ("analysis/effects/expression_forms.py", "_impl__clone_expression_tree", "clone_with_operands"): 1,
    ("analysis/effects/expression_forms.py", "_impl__clone_expression_with_operands", "copied_expr_type_with_operands"): 1,
    ("analysis/effects/post_state.py", "_impl__rewrite_definite_post_state_subexpressions", "copied_runtime_ref"): 1,
    ("analysis/effects/post_state.py", "_impl__rewrite_expression_with_replayed_state", "copied_runtime_ref"): 1,
    ("analysis/effects/post_state.py", "_impl_collapse_equivalent_post_state_subexpressions", "copied_runtime_ref"): 1,
    ("analysis/effects/post_state.py", "_impl_promote_effect_subexpressions_to_post_state_reads", "copied_runtime_ref"): 1,
    ("analysis/effects/post_state.py", "_impl_promote_observed_loads_to_post_state_reads", "copied_runtime_ref"): 1,
    ("analysis/effects/post_state.py", "_impl_rewrite_loads_from_effects", "copied_runtime_ref"): 1,
    ("analysis/effects/post_state.py", "_impl_rewrite_observed_loads_from_effects", "copied_runtime_ref"): 1,
    ("analysis/memory_resolver.py", "_rewrite_expr", "clone_with_operands"): 2,
    ("analysis/memory_resolver.py", "_split_conditional_offset_load", "clone_with_operands"): 2,
    ("analysis/memory_resolver.py", "_split_memory_address_phi", "clone_with_operands"): 1,
    ("analysis/recurrence/coordinator.py", "_impl__substitute_generated_loop_variable_aliases", "copied_runtime_ref"): 2,
    ("analysis/recurrence/object_identity.py", "_impl__canonicalize_expression_parameters_for_analysis", "copied_expr_type_with_operands"): 1,
    ("analysis/recurrence/proof_utils.py", "_impl__clone_summary_expression_for_smt", "clone_with_operands"): 1,
    ("analysis/recurrence/proof_utils.py", "_impl__copy_symbol_expression", "copied_runtime_ref"): 2,
    ("analysis/recurrence/proof_utils.py", "_impl__substitute_exact_expression", "copied_runtime_ref"): 2,
    ("analysis/returns/call_recovery.py", "_impl__normalize_call_target_expression", "clone_with_operands"): 1,
    ("analysis/returns/call_recovery.py", "_impl__normalize_callother_userop_expression", "clone_with_operands"): 1,
    ("analysis/returns/call_recovery.py", "_impl__normalize_callother_userop_expression", "copied_runtime_ref"): 1,
    ("analysis/returns/call_recovery.py", "_impl__rewrite_deferred_runtime_refs_in_expression", "clone_with_operands"): 1,
    ("analysis/returns/condition_logic.py", "ConditionLogicService.evaluate_expression_under_parameter_assignments", "clone_with_operands"): 1,
    ("analysis/returns/condition_logic.py", "ConditionLogicService.reduce_phi_expression_under_conditions_with_smt", "clone_with_operands"): 1,
    ("analysis/returns/condition_logic.py", "ConditionLogicService.substitute_parameter_constants", "clone_with_operands"): 1,
    ("analysis/returns/effect_integration.py", "EffectIntegrationService.rebuild_effect_sensitive_case_wrapper", "clone_with_operands"): 1,
    ("analysis/returns/expression_cases.py", "ExpressionCaseService.expand_object_centric_expression_cases", "clone_with_operands"): 3,
    ("analysis/returns/expression_cases.py", "clone_expression", "clone_with_operands"): 1,
    ("analysis/returns/summary_returns.py", "_canonicalize_expression_parameters_for_analysis", "copied_expr_type_with_operands"): 1,
    ("analysis/switch.py", "_clone_expression", "clone_with_operands"): 1,
    ("analysis/switch.py", "_expand_expression_cases", "clone_with_operands"): 1,
    ("analysis/switch.py", "_replace_expression_node", "clone_with_operands"): 1,
    ("analysis/tracer.py", "PcodeTracer._clone_expression", "copied_expr_type_with_operands"): 1,
    ("core/analysis.py", "_rewrite_expression_for_param_signedness", "clone_with_operands"): 1,
    ("proof/conditional_view.py", "_rewrite_expression", "copied_expr_type_with_operands"): 1,
    ("proof/deferred_call_abstraction.py", "_rewrite_expression", "copied_expr_type_with_operands"): 1,
    ("proof/formula/builder.py", "_rewrite_expr_parameter_metadata_for_smt", "copied_expr_type_with_operands"): 1,
    ("proof/formula/builder.py", "_rewrite_parameter_leaf_for_smt", "copied_expr_type_with_operands"): 1,
    ("proof/strategies/loop_template.py", "_substitute_exact_replacements", "copied_expr_type_with_operands"): 1,
    ("proof/strategies/pairwise_services/auxiliary_smt.py", "_impl__clone_auxiliary_expression_for_smt", "clone_with_operands"): 2,
    ("proof/strategies/pairwise_services/case_conditions.py", "_impl__replace_expression_node", "clone_with_operands"): 1,
    ("proof/strategies/pairwise_services/loop_summary.py", "_impl__counted_loop_bounded_state_transition_base_candidate", "clone_with_operands"): 1,
    ("proof/strategies/pairwise_services/pair_cases.py", "_impl__conditions_with_object_identity_parameter_symbols.clone_expr", "clone_with_operands"): 1,
    ("semantics/normalize/arithmetic.py", "_rewrite_sub_as_add_neg", "clone_with_operands"): 1,
    ("semantics/normalize/core.py", "normalize_expression", "clone_with_operands"): 1,
    ("semantics/normalize/division.py", "_normalize_double_negated_division", "clone_with_operands"): 1,
    ("semantics/normalize/division.py", "_normalize_negated_division", "clone_with_operands"): 2,
    ("semantics/normalize/division_signedness.py", "normalize_division_signedness", "clone_with_operands"): 1,
    ("semantics/normalize/division_signedness_guarded.py", "_try_convert_udiv_to_sdiv", "clone_with_operands"): 1,
    ("semantics/normalize/division_signedness_guarded.py", "normalize_udiv_with_guard", "clone_with_operands"): 1,
    ("semantics/normalize/series.py", "_clone_expression", "copied_expr_type_with_operands"): 1,
    ("semantics/semantic_width.py", "SemanticWidthNormalizer._widen_zero_comparison_constant", "clone_with_operands"): 1,
    ("semantics/semantic_width.py", "SemanticWidthNormalizer.rewrite_expression", "copied_expr_type_with_operands"): 1,
    ("semantics/semantic_width.py", "_rewrite_parameter_expression_metadata", "copied_expr_type_with_operands"): 2,
    ("semantics/transform/expander.py", "ExpressionExpander._expand_expression_cases", "copied_runtime_ref"): 1,
    ("semantics/transform/expander_canonical.py", "CanonicalizationMixin._canonicalize_expression_to_location_leaf", "clone_with_operands"): 1,
}


def _reads_attribute(node: ast.AST, attribute: str) -> bool:
    """``<式>.attribute`` か ``getattr(<式>, "attribute", ...)``。"""

    if isinstance(node, ast.Attribute) and node.attr == attribute:
        return True
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "getattr"
        and len(node.args) >= 2
        and isinstance(node.args[1], ast.Constant)
        and node.args[1].value == attribute
    )


class _OperandSiteVisitor(ast.NodeVisitor):
    def __init__(self, rel_path: str) -> None:
        self.rel_path = rel_path
        self.scope = []
        self.sites = Counter()

    def _site(self, kind: str) -> None:
        self.sites[(self.rel_path, ".".join(self.scope) or "<module>", kind)] += 1

    def _visit_scope(self, node) -> None:
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()

    visit_FunctionDef = _visit_scope
    visit_AsyncFunctionDef = _visit_scope
    visit_ClassDef = _visit_scope

    def visit_Call(self, node: ast.Call) -> None:
        keywords = {keyword.arg for keyword in node.keywords}
        func = node.func
        name = func.id if isinstance(func, ast.Name) else getattr(func, "attr", None)
        counted = False
        if isinstance(func, ast.Attribute) and name in ("clone_with", "derive_with"):
            # `**fields` は operand を含み得る（名前を見られない）
            if "operands" in keywords or None in keywords:
                self._site(f"{name}_operands")
                counted = True
        if name == "Expression":
            expr_type = node.args[0] if node.args else next(
                (keyword.value for keyword in node.keywords if keyword.arg == "expr_type"), None
            )
            # `operands` は 4 番目の位置引数でも渡せる（`Expression(expr_type, value, operator, operands)`）
            if ("operands" in keywords or len(node.args) >= 4) and expr_type is not None and _reads_attribute(
                expr_type, "expr_type"
            ):
                self._site("copied_expr_type_with_operands")
                counted = True
        if not counted:
            runtime_ref = next((keyword.value for keyword in node.keywords if keyword.arg == "runtime_ref"), None)
            if runtime_ref is not None and _reads_attribute(runtime_ref, "runtime_ref"):
                self._site("copied_runtime_ref")
        if name in ("setattr", "__setattr__") and any(
            isinstance(argument, ast.Constant) and argument.value == "operands" for argument in node.args[1:2]
        ):
            self._site("operands_store")
        self.generic_visit(node)

    def _store_target(self, target: ast.AST) -> None:
        if isinstance(target, ast.Attribute) and target.attr == "operands":
            self._site("operands_store")
        elif isinstance(target, ast.Subscript) and isinstance(target.value, ast.Attribute):
            if target.value.attr == "operands" or (
                target.value.attr == "__dict__"
                and isinstance(target.slice, ast.Constant)
                and target.slice.value == "operands"
            ):
                self._site("operands_store")
        elif isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._store_target(element)

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self._store_target(target)
        self.generic_visit(node)

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self._store_target(node.target)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None:
            self._store_target(node.target)
        self.generic_visit(node)


def _scan_source(rel_path: str, source: str) -> Counter:
    visitor = _OperandSiteVisitor(rel_path)
    visitor.visit(ast.parse(source))
    return visitor.sites


@functools.lru_cache(maxsize=1)
def _scan_package() -> Counter:
    sites = Counter()
    for directory, dirnames, filenames in os.walk(PACKAGE_ROOT):
        dirnames[:] = [name for name in dirnames if name not in {"tests", "__pycache__"}]
        for filename in filenames:
            if not filename.endswith(".py"):
                continue
            path = os.path.join(directory, filename)
            rel_path = os.path.relpath(path, PACKAGE_ROOT).replace(os.sep, "/")
            with open(path, encoding="utf-8") as handle:
                sites.update(_scan_source(rel_path, handle.read()))
    return sites


def test_no_new_operand_substitution_outside_derive_with_operands():
    found = _scan_package()
    unexpected = {
        key: count
        for key, count in found.items()
        if key not in OWNER_SITES and count > BASELINE.get(key, 0)
    }
    assert not unexpected, (
        "operand を差し替えた node は Expression.derive_with_operands で作る（Issue #281）: "
        f"{sorted(unexpected.items())}"
    )


def test_operand_substitution_baseline_has_no_stale_entries():
    found = _scan_package()
    stale = {key: (count, found.get(key, 0)) for key, count in BASELINE.items() if found.get(key, 0) < count}
    assert not stale, f"baseline は削るだけ: 減った site の行を消す（baseline, 実際）: {sorted(stale.items())}"
    assert all(key in found for key in OWNER_SITES)


def test_the_guard_detects_every_form():
    source = (
        "def rebuild(expr, operands, fields):\n"
        "    a = expr.clone_with(operands=operands)\n"
        "    b = Expression(expr.expr_type, operands=operands)\n"
        "    c = Expression(expr_type=node.expr_type, operands=operands, opcode=1)\n"
        "    d = Expression(expr.expr_type, None, None, operands)\n"
        "    e = expr.derive_with(operands=operands)\n"
        "    f = expr.derive_with(**fields)\n"
        "    g = expr.clone_with(**fields)\n"
        "    h = Expression.memory(operands[0], 8, runtime_ref=expr.runtime_ref)\n"
        "    i = Expression.intrinsic('PTRADD', operands, runtime_ref=getattr(expr, 'runtime_ref', None))\n"
        "    expr.operands = operands\n"
        "    expr.operands[0] = operands[0]\n"
        "    setattr(expr, 'operands', operands)\n"
        "    object.__setattr__(expr, 'operands', operands)\n"
        "    expr.__dict__['operands'] = operands\n"
    )
    assert _scan_source("x.py", source) == Counter({
        ("x.py", "rebuild", "clone_with_operands"): 2,
        ("x.py", "rebuild", "derive_with_operands"): 2,
        ("x.py", "rebuild", "copied_expr_type_with_operands"): 3,
        ("x.py", "rebuild", "copied_runtime_ref"): 2,
        ("x.py", "rebuild", "operands_store"): 5,
    })


def test_the_guard_leaves_legitimate_forms_alone():
    source = (
        "def ok(expr, left, right):\n"
        "    a = expr.clone_with(size=4)\n"
        "    b = expr.derive_with(size=8)\n"
        "    c = Expression(ExpressionType.BINARY_OP, operator='INT_ADD', operands=[left, right])\n"
        "    d = Expression.binary_op('INT_ADD', left, right)\n"
        "    e = expr.derive_with_operands([left, right])\n"
        "    f = Expression.memory(left, 8, runtime_ref=PostStateReadRef(location))\n"
        "    g = expr.operands[0]\n"
    )
    assert _scan_source("x.py", source) == Counter()


def test_derive_with_refuses_operands_at_runtime():
    """`derive_with` は operand を差し替えない（`**` で渡しても止まる。AST に見えない経路の実行時の担保）。"""

    from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType

    left = Expression(ExpressionType.PARAMETER, name="param_1", size=4)
    right = Expression(ExpressionType.PARAMETER, name="param_2", size=4)
    node = Expression(ExpressionType.BINARY_OP, operator="INT_ADD", operands=[left, right], size=4)
    with pytest.raises(TypeError, match="derive_with_operands"):
        node.derive_with(operands=[right, left])
    fields = {"operands": [right, left], "size": 8}
    with pytest.raises(TypeError, match="derive_with_operands"):
        node.derive_with(**fields)
    assert node.derive_with(size=8).size == 8
