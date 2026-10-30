# -*- coding: utf-8 -*-
"""operand を差し替えた式を、`derive_with_operands` 以外で作る新しい書き方を禁じる（Issue #281）。

#281 は、node を operand だけ差し替えて作り直す site が field（`opcode`）を落としたことから起きた。
field と runtime ref の扱いの owner は `core/operand_derivation.py`（`Expression.derive_with_operands`）
1 つにする。この test は、owner を通らずに **既存の node を写して operand を差し替える** 書き方を AST で
数える:

* ``<式>.clone_with(..., operands=...)`` — 写した ref・field をそのまま新しい operand に付ける
* ``Expression(<式>.expr_type, ..., operands=...)`` — 既存の node の種類を写して作り直す（#281 の形）

既存の site は `BASELINE` に (file, 関数の qualname, 種類) ごとの数で入れてある。**baseline は削るだけ**:

* baseline に無い site・数が増えた site は失敗する（新しい site は `derive_with_operands` を使う）
* site を `derive_with_operands` へ移したら、その行を消す（数が減ったのに baseline が古いままでも失敗する）

数えないもの（この guard の限界）: factory で一から作り直す書き方（``Expression.binary_op(expr.operator,
...)`` 等。ref を写さないので古い ref は残らないが、field を落とし得る）と、`copy` の後の代入。前者は
件数が多く、ref を持たない node の正規化が大半なので対象にしていない。
"""

import ast
import functools
import os
from collections import Counter

PACKAGE_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

#: owner そのもの（ここだけが operand を差し替えた node を作ってよい）
OWNER_SITES = frozenset({("core/operand_derivation.py", "derive_with_operands", "copied_expr_type_with_operands")})

#: 既存の site（Issue #281 の時点）。削るだけ。移した site の行は消す
BASELINE = {
    ("analysis/condition/simplifier.py", "ConditionSimplifier._reduce_expression_under_conditions", "copied_expr_type_with_operands"): 1,
    ("analysis/condition/smt_oracle.py", "ConditionSMTOracle._rewrite_expr_with_symbol_names", "clone_with_operands"): 1,
    ("analysis/effects/expression_forms.py", "_impl__clone_expression_tree", "clone_with_operands"): 1,
    ("analysis/effects/expression_forms.py", "_impl__clone_expression_with_operands", "copied_expr_type_with_operands"): 1,
    ("analysis/memory_resolver.py", "_rewrite_expr", "clone_with_operands"): 2,
    ("analysis/memory_resolver.py", "_split_conditional_offset_load", "clone_with_operands"): 2,
    ("analysis/memory_resolver.py", "_split_memory_address_phi", "clone_with_operands"): 1,
    ("analysis/recurrence/proof_utils.py", "_impl__clone_summary_expression_for_smt", "clone_with_operands"): 1,
    ("analysis/returns/call_recovery.py", "_impl__normalize_call_target_expression", "clone_with_operands"): 1,
    ("analysis/returns/call_recovery.py", "_impl__normalize_callother_userop_expression", "clone_with_operands"): 1,
    ("analysis/returns/call_recovery.py", "_impl__rewrite_deferred_runtime_refs_in_expression", "clone_with_operands"): 1,
    ("analysis/returns/condition_logic.py", "ConditionLogicService.evaluate_expression_under_parameter_assignments", "clone_with_operands"): 1,
    ("analysis/returns/condition_logic.py", "ConditionLogicService.reduce_phi_expression_under_conditions_with_smt", "clone_with_operands"): 1,
    ("analysis/returns/condition_logic.py", "ConditionLogicService.substitute_parameter_constants", "clone_with_operands"): 1,
    ("analysis/returns/effect_integration.py", "EffectIntegrationService.rebuild_effect_sensitive_case_wrapper", "clone_with_operands"): 1,
    ("analysis/returns/expression_cases.py", "ExpressionCaseService.expand_object_centric_expression_cases", "clone_with_operands"): 3,
    ("analysis/returns/expression_cases.py", "clone_expression", "clone_with_operands"): 1,
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
    ("semantics/transform/expander_canonical.py", "CanonicalizationMixin._canonicalize_expression_to_location_leaf", "clone_with_operands"): 1,
}


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
        if "operands" in keywords:
            if isinstance(func, ast.Attribute) and func.attr == "clone_with":
                self._site("clone_with_operands")
            name = func.id if isinstance(func, ast.Name) else getattr(func, "attr", None)
            if name == "Expression":
                expr_type = node.args[0] if node.args else next(
                    (keyword.value for keyword in node.keywords if keyword.arg == "expr_type"), None
                )
                if isinstance(expr_type, ast.Attribute) and expr_type.attr == "expr_type":
                    self._site("copied_expr_type_with_operands")
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


def test_the_guard_detects_both_forms():
    source = (
        "def rebuild(expr, operands):\n"
        "    a = expr.clone_with(operands=operands)\n"
        "    b = Expression(expr.expr_type, operands=operands)\n"
        "    c = Expression(expr_type=node.expr_type, operands=operands, opcode=1)\n"
        "    d = Expression(ExpressionType.BINARY_OP, operands=operands)\n"
        "    e = expr.clone_with(size=4)\n"
    )
    assert _scan_source("x.py", source) == Counter({
        ("x.py", "rebuild", "clone_with_operands"): 1,
        ("x.py", "rebuild", "copied_expr_type_with_operands"): 2,
    })
