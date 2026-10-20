"""SMT-LIB rendering of expressions: core renderer, width coercion, float theory, loop lowerings, intrinsics and unknown-symbol declarations.

描画は DAG を 1 回だけ辿る反復実装（`core/render_plan`）で、共有部分式は
`let` で 1 回だけ定義する（`bindings`）。描画文脈（`context`）が違う同じ node は
別の束縛になる。node 属性の評価（幅 / Bool sort / 符号拡張の好み）は
`attributes` が反復 + DAG memo で回す。

**この package が外へ出す面は描画の入口だけ**（`expression_to_smt` /
`condition_to_smt` / 証拠用の 2 つ / `render_smt_term` / `SMT_RENDER_SCHEMA`）。
共有方針・束縛名・型付きの項・属性評価は描画の実装どうしの取り決めなので、
`bindings` / `context` / `attributes` / `render` を直接 import する側だけが見る。
外へ出すと、共有の条件や性質の持ち方を変えるたびに外部 consumer が壊れる。
ここに並ぶそれ以外の名前は PR-22-C より前からある再 export（既存 import の互換）。
"""

from scripts.function_tracer_pcode.core.render_smt.bindings import (  # noqa: F401
    SMT_RENDER_SCHEMA,
)
from scripts.function_tracer_pcode.core.render_smt.calls import (  # noqa: F401
    CallDeclarationConflict,
    CallSmtDeclarations,
    add_call_smt_declaration,
    call_smt_declaration,
    call_smt_declaration_lines,
    collect_call_smt_declarations,
    expression_contains_call,
)
from scripts.function_tracer_pcode.core.render_smt.float_theory import (  # noqa: F401
    FLOAT_SEMANTICS_PCODE_OPERATORS,
    _FLOAT_PREDICATE_FP_OPS,
    _FLOAT_UNARY_PREDICATE_SMT_NAMES,
    _FLOAT_UNARY_VALUE_SMT_NAMES,
    _bitvec_to_fp_smt,
    _float_binary_can_use_fp_theory,
    _float_binary_can_use_fp_theory_for_operator,
    _float_binary_has_known_exceptional_operand,
    _float_binary_to_smt,
    _float_predicate_can_use_fp_theory,
    _float_predicate_to_smt,
    _float_unary_predicate_to_smt,
    _float_unary_to_bitvec_smt,
    _float_unary_value_to_smt,
    _is_float_rendered_expr,
    _looks_like_fp_expr,
    _normalize_to_fp_expr,
    collect_float_predicate_smt_declarations,
    expression_node_uses_float_pcode_operator,
    expression_renders_as_fp_sort,
    expression_smt_sort_kind,
    expression_uses_float_pcode_operators,
    expression_uses_smt_float_theory,
)
from scripts.function_tracer_pcode.core.render_smt.intrinsics import (  # noqa: F401
    _intrinsic_result_bits,
    _intrinsic_smt_declaration,
    _lower_intrinsic_to_smt,
    collect_intrinsic_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.loop_lowering import (  # noqa: F401
    _constant_multiplier_pow_smt,
    _counted_loop_sum_exact_smt,
    _counted_loop_sum_function_name,
    _counted_loop_sum_has_exact_lowering,
    _counted_state_transition_exact_smt,
    _counted_state_transition_value_function_name,
    _counted_state_transition_value_has_exact_lowering,
    _lower_neon_ext_operands_to_smt,
    _neon_ext_operands_are_smt_supported,
    _readonly_sum_function_name,
    _state_transition_loop_count_function_name,
)
from scripts.function_tracer_pcode.core.render_smt.render import (  # noqa: F401
    SMT_SEMANTICS_REFUSALS,
    UnknownSmtExtensionWidthError,
    UnsupportedSmtIntrinsicError,
    UnsupportedSmtOperatorError,
    UnsupportedSmtSemanticsError,
    _ARITHMETIC_BINARY_OPERATORS,
    _BITWISE_BINARY_OPERATORS,
    _BOOLEAN_BINARY_OPERATORS,
    _FLOAT_ARITHMETIC_FP_OPS,
    _FLOAT_ARITHMETIC_FP_SPECS,
    _FLOAT_ARITHMETIC_SMT_NAMES,
    _FLOAT_BV_WIDTH_TO_SORT,
    _FLOAT_PREDICATE_SMT_NAMES,
    _MEMORY_ARRAY_WIDTHS,
    _SIGNED_COMPARISON_OPERATORS,
    _SMT_IDENTIFIER_RE,
    _SUPPORTED_BINARY_OPERATORS,
    _SUPPORTED_UNARY_OPERATORS,
    _coerce_bool_to_bitvec,
    _coerce_expr_to_bool,
    _to_smt_internal,
    render_smt_term,
    expression_contains_signed_comparison,
    expression_contains_unsupported_smt_ops,
    expression_node_has_unsupported_smt_ops,
    expression_returns_bool,
    expression_to_smt,
    condition_to_smt,
    render_condition_smt_evidence,
    render_expression_smt_evidence,
    expression_uses_smt_uf,
    get_smt_operator,
    normalize_call_symbol_name,
    smt_logic_name,
)
from scripts.function_tracer_pcode.core.render_smt.unknowns import (  # noqa: F401
    _iter_expression_nodes,
    _unknown_runtime_identity_key,
    _unknown_smt_declaration,
    _unknown_smt_symbol_name,
    collect_unknown_smt_declarations,
    collect_global_address_identities,
    global_address_identity,
    global_address_smt,
    global_address_symbol_name,
    GLOBAL_ADDRESS_BITS,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (  # noqa: F401
    _coerce_expr_to_bitvec_width,
    _coerce_smt_bitvec_width,
    _constant_fits_width,
    _expr_constant_int,
    _expr_is_known_nan_or_inf_bitpattern,
    _expr_is_known_zero_bitpattern,
    _expr_prefers_signed_extension,
    _piece_subpiece_contract,
    _piece_subpiece_width_issue,
    _preferred_arithmetic_width,
    _rewrite_ambiguous_negative_constant,
    _safe_size_bytes,
    _smt_bv_const,
    _smt_concat,
    _smt_extend_to_width,
    _smt_extract,
    _smt_low_bits,
    _smt_scale_term,
    _smt_width_if_known,
    expression_smt_bit_width,
)

