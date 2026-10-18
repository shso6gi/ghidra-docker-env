"""Core expression -> SMT-LIB renderer, operator table, logic selection and unsupported-op detection."""

from __future__ import annotations

import hashlib
import re
from typing import Any, Mapping, NamedTuple, Optional
from scripts.function_tracer_pcode.core.intrinsics import is_supported_pcode_intrinsic
from scripts.function_tracer_pcode.core.render_smt.attributes import (
    any_node,
    attribute_cache,
    evaluate_attribute,
    render_attribute_scope,
)
from scripts.function_tracer_pcode.core.render_output import (
    CountingWriter,
    RenderCounters,
    RenderOutputLimitExceeded,
    utf8_length,
)
from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetKind,
    active_budget_policy,
    observe_budget_usage,
    raise_render_budget_exceeded,
)
from scripts.function_tracer_pcode.core.render_metrics import record_render
from scripts.function_tracer_pcode.core.render_plan import (
    NO_SHARING_POLICY,
    FragmentBuilder,
    RenderGraphCycleError,
    RenderPlanInvariantError,
    RenderedTerm,
    build_render_plan,
    check_plan_invariants,
    term_properties,
)
from scripts.function_tracer_pcode.core.render_smt.bindings import (
    SMT_SHARING_POLICY,
    assign_binding_names,
    smt_binding_namespace,
    write_let_term,
)
from scripts.function_tracer_pcode.core.render_smt.context import (
    SmtRenderContext,
    build_smt_render_context,
)
from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    SemanticLifecycle,
    state_of,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    semantic_projection,
    traverse_semantic_graph,
)


_BOOLEAN_BINARY_OPERATORS = {
    "INT_EQUAL",
    "INT_NOTEQUAL",
    "INT_LESS",
    "INT_SLESS",
    "INT_LESSEQUAL",
    "INT_SLESSEQUAL",
    "FLOAT_EQUAL",
    "FLOAT_NOTEQUAL",
    "FLOAT_LESS",
    "FLOAT_LESSEQUAL",
    "BOOL_AND",
    "BOOL_OR",
    "BOOL_XOR",
}


_SIGNED_COMPARISON_OPERATORS = {
    "INT_SLESS",
    "INT_SLESSEQUAL",
}


_FLOAT_PREDICATE_SMT_NAMES = {
    "FLOAT_EQUAL": "float_equal",
    "FLOAT_NOTEQUAL": "float_notequal",
    "FLOAT_LESS": "float_less",
    "FLOAT_LESSEQUAL": "float_lessequal",
}


_FLOAT_ARITHMETIC_SMT_NAMES = {
    "FLOAT_ADD": "float_add",
    "FLOAT_SUB": "float_sub",
    "FLOAT_MULT": "float_mult",
    "FLOAT_DIV": "float_div",
    "FLOAT_SDIV": "float_div",
    "FLOAT_REM": "float_rem",
    "FLOAT_SREM": "float_rem",
}


_FLOAT_ARITHMETIC_FP_OPS = {
    "FLOAT_ADD": "fp.add",
    "FLOAT_SUB": "fp.sub",
    "FLOAT_MULT": "fp.mul",
    "FLOAT_DIV": "fp.div",
    "FLOAT_SDIV": "fp.div",
    "FLOAT_REM": "fp.rem",
    "FLOAT_SREM": "fp.rem",
}


_FLOAT_ARITHMETIC_FP_SPECS = {
    "FLOAT_ADD": {"fp_op": "fp.add", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_SUB": {"fp_op": "fp.sub", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_MULT": {"fp_op": "fp.mul", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_DIV": {"fp_op": "fp.div", "rounding": True, "guard_known_exceptional_operands": False},
    "FLOAT_REM": {"fp_op": "fp.rem", "rounding": False, "guard_known_exceptional_operands": False},
    "FLOAT_SDIV": {"fp_op": "fp.div", "rounding": True, "guard_known_exceptional_operands": True},
    "FLOAT_SREM": {"fp_op": "fp.rem", "rounding": False, "guard_known_exceptional_operands": True},
}


_FLOAT_BV_WIDTH_TO_SORT = {
    32: (8, 24),
    64: (11, 53),
}


_MEMORY_ARRAY_WIDTHS = {8, 16, 32, 64}


_SMT_IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


_ARITHMETIC_BINARY_OPERATORS = {
    "INT_AND",
    "INT_OR",
    "INT_XOR",
    "INT_ADD",
    "INT_SUB",
    "INT_MULT",
    "INT_DIV",
    "INT_SDIV",
    "INT_REM",
    "INT_SREM",
}


_BITWISE_BINARY_OPERATORS = {"INT_AND", "INT_OR", "INT_XOR"}


_SUPPORTED_BINARY_OPERATORS = (
    _ARITHMETIC_BINARY_OPERATORS
    | _BOOLEAN_BINARY_OPERATORS
    | set(_FLOAT_ARITHMETIC_SMT_NAMES.keys())
    | {"PIECE", "SUBPIECE", "INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}
)


_SUPPORTED_UNARY_OPERATORS = {
    "INT2FLOAT",
    "INT_ZEXT",
    "INT_SEXT",
    "INT_NEGATE",
    "INT_2COMP",
    "BOOL_NEGATE",
    "FLOAT_NEG",
    "FLOAT_ABS",
    "FLOAT_SQRT",
    "FLOAT_NAN",
}


class UnsupportedSmtSemanticsError(ValueError):
    """Base class for typed refusals of unavailable exact SMT semantics.

    ``refusal_evidence_ref`` / ``refusal_target_fields()`` are the refusal's typed identity (what the
    strategies put into their ``expression_semantics_unsupported`` diagnostic); the message text is
    diagnostic only.
    """

    refusal_evidence_ref = "unsupported_smt_semantics"

    def refusal_target_fields(self) -> tuple:
        return (self.refusal_evidence_ref, type(self).__name__)


class UnsupportedSmtIntrinsicError(UnsupportedSmtSemanticsError):
    """Typed semantic-lowering refusal; message text is diagnostic only."""

    def __init__(self, *, mnemonic: Optional[str], opcode: Optional[str]) -> None:
        self.mnemonic = mnemonic
        self.opcode = opcode
        self.intrinsic_identity = mnemonic or opcode
        super().__init__(
            f"Unsupported intrinsic for SMT lowering: {self.intrinsic_identity}"
        )

    refusal_evidence_ref = "unsupported_intrinsic_smt_lowering"

    def refusal_target_fields(self) -> tuple:
        return ("unsupported_smt_intrinsic", self.intrinsic_identity)


class UnknownSmtExtensionWidthError(ValueError):
    """Typed refusal to lower an extension without its P-code output width."""

    def __init__(self, *, operator: str, operand_bits: int) -> None:
        self.operator = operator
        self.operand_bits = int(operand_bits)
        super().__init__(
            f"{operator} output width is unavailable "
            f"(operand width: {self.operand_bits or 'unknown'} bits)"
        )

    refusal_evidence_ref = "unknown_smt_extension_width"

    def refusal_target_fields(self) -> tuple:
        return (self.refusal_evidence_ref, self.operator, self.operand_bits)


class UnsupportedSmtOperatorError(UnsupportedSmtSemanticsError):
    """Typed refusal for an operator that has no exact SMT lowering."""

    def __init__(
        self,
        *,
        operator: Optional[str],
        reason: str,
        operand_bits: int = 0,
        result_bits: int = 0,
    ) -> None:
        self.operator = operator
        self.reason = reason
        self.operand_bits = int(operand_bits or 0)
        self.result_bits = int(result_bits or 0)
        super().__init__(
            f"{operator or 'unknown operator'} has no exact SMT lowering: {reason} "
            f"(operand width: {self.operand_bits or 'unknown'} bits, "
            f"result width: {self.result_bits or 'unknown'} bits)"
        )

    refusal_evidence_ref = "unsupported_smt_operator"

    def refusal_target_fields(self) -> tuple:
        return (
            self.refusal_evidence_ref, self.operator, self.reason, self.operand_bits, self.result_bits,
        )


#: 正確な SMT の意味が無いことを示す型つきの拒否の全て（strategy が UNKNOWN にする族）。
#: ``UnknownSmtExtensionWidthError`` は歴史的に ``UnsupportedSmtSemanticsError`` の外にあるので並べる。
SMT_SEMANTICS_REFUSALS = (UnsupportedSmtSemanticsError, UnknownSmtExtensionWidthError)


#: solver へ渡す描画の出力を観測・予算判定する点（書き出し口は `CountingWriter`）。
SOLVER_RENDER_SITE = "core.render_smt.emit"


def expression_to_smt(
    expr,
    *,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    float_mode: str = "uf",
    shared: bool = True,
) -> str:
    """式を **solver へ渡す** SMT-LIB 文字列へ変換する。

    入力は **公開済み**（`core/semantic_freeze.publish`）でなければならない。
    未公開なら typed な内部バグとして落とす。ここで代わりに公開してしまうと、
    「この値はもう確定した」と誰も言っていない中間値から判定用の論理式が作れて
    しまい、公開点を持たない producer がいつまでも見つからない。

    描画は式の lifecycle を進めない — consumer は状態を読むだけで、値が確定した
    と宣言できるのは作った側だけ。producer 別・型別の分岐もここには置かない
    （どの種類の式でも「公開済みか」だけを見る）。

    凍らせられない graph（閉路）は公開の時点で落ちるので、placeholder を入れた
    論理式が solver へ届くことはない。

    証拠・表示のためのテキストが欲しいときは `render_expression_smt_evidence()`
    を使うこと。あちらは solver へ渡さない前提なので、公開を要求しない。
    """

    if expr is not None and not _is_published_semantic_input(expr):
        raise _unpublished_semantic_input(expr)
    # Issue #22 PR-22-D: solver へ渡す描画だけに出力予算を当てる。証拠・表示用の
    # 入口（下の 2 つ）は判定に使わないので予算で pair を止めない。
    try:
        text = _to_smt_internal(
            expr,
            symbol_name_mapping=symbol_name_mapping,
            float_mode=float_mode,
            shared=shared,
            limit_bytes=active_budget_policy().render_bytes,
        )
    except RenderOutputLimitExceeded as exc:
        raise_render_budget_exceeded(exc, subject=expr)
    observe_budget_usage(BudgetKind.RENDER_BYTES, utf8_length(text), site=SOLVER_RENDER_SITE)
    return text


def render_expression_smt_evidence(
    expr,
    *,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    float_mode: str = "uf",
    shared: bool = True,
) -> str:
    """**証拠・表示のための** SMT 風テキスト（solver へは渡さない）。

    書き換え規則が「この式がこの式になった」と記録するときの before / after や、
    人向けの report がこれを使う。記録の対象はまだ組み立て中の中間値でよいので、
    `expression_to_smt()` のように検証済みを要求しない。

    逆に言うと、**ここで作った文字列を solver へ渡してはいけない**。判定に使う
    論理式は確定した意味から作る必要があり、その入口は `expression_to_smt()`
    だけ。呼び分けを型ではなく関数名で見えるようにしてあるのは、「どちらの
    consumer か」が call site で分かる方が後から追いやすいため。
    """

    return _to_smt_internal(
        expr,
        symbol_name_mapping=symbol_name_mapping,
        float_mode=float_mode,
        shared=shared,
    )


def condition_to_smt(
    condition,
    *,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    float_mode: str = "uf",
    shared: bool = True,
) -> str:
    """条件を **solver へ渡す** SMT-LIB 文字列へ変換する。

    式と同じ契約: 公開済みの条件しか受け取らない（`Condition.to_smt` の実体）。
    条件も「この式がこの向きで成り立つ」という 1 つの意味の単位なので、
    lifecycle も式と同じ。
    """

    if condition is not None and not _is_published_semantic_input(condition):
        raise _unpublished_semantic_input(condition)
    try:
        text = _condition_to_smt_internal(
            condition,
            symbol_name_mapping=symbol_name_mapping,
            float_mode=float_mode,
            shared=shared,
            limit_bytes=active_budget_policy().render_bytes,
        )
    except RenderOutputLimitExceeded as exc:
        raise_render_budget_exceeded(exc, subject=condition)
    observe_budget_usage(BudgetKind.RENDER_BYTES, utf8_length(text), site=SOLVER_RENDER_SITE)
    return text


def render_condition_smt_evidence(
    condition,
    *,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    float_mode: str = "uf",
    shared: bool = True,
) -> str:
    """**証拠・表示のための** 条件テキスト（solver へは渡さない）。"""

    return _condition_to_smt_internal(
        condition,
        symbol_name_mapping=symbol_name_mapping,
        float_mode=float_mode,
        shared=shared,
    )


def _condition_to_smt_internal(
    condition,
    *,
    prefer_sign_extension: bool = False,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    address_context: Any = None,
    float_mode: str = "uf",
    shared: bool = True,
    limit_bytes: Optional[int] = None,
) -> str:
    """条件の描画入口。**renderer 内部の再帰はここを通らない**。

    条件も 1 つの描画 instance なので、式と同じ driver で描く（PHI の branch
    条件から共有できるのもこのため）。入口が公開検査を持つのは外から来た値だけ
    で、内部は driver が直接 node 本体を呼ぶ。
    """

    if condition is None:
        return "true"
    context = build_smt_render_context(
        prefer_signed_arithmetic=prefer_sign_extension,
        address_context=address_context,
        float_mode=float_mode,
        symbol_name_mapping=symbol_name_mapping,
    )
    return render_smt_term(
        condition,
        context,
        symbol_name_mapping,
        shared=shared,
        limit_bytes=limit_bytes,
    )


_EXPRESSION_TYPE = None
_CONDITION_TYPE = None


def _unpublished_semantic_input(expr):
    """未公開入力を内部バグとして記録し、typed failure を作る。

    記録してから raise するので、途中の `except Exception` に握り潰されても
    pair 境界が台帳から拾い直して `internal_exception` の ERROR にできる。
    renderer 側に producer 別・型別の分岐は置かない。
    """

    from scripts.function_tracer_pcode.core.errors import (
        UnpublishedSemanticInputError,
        record_internal_bug,
    )

    expr_type = getattr(expr, "expr_type", None)
    kind = getattr(expr_type, "name", None) if expr_type is not None else "CONDITION"
    exc = UnpublishedSemanticInputError(
        f"solver SMT generation received an unpublished {kind} value; "
        "publish it where it is produced (see core/semantic_freeze.publish)"
    )
    record_internal_bug(exc, site="core.render_smt.expression_to_smt")
    return exc


def _is_published_semantic_input(expr) -> bool:
    """producer が公開を宣言した意味 object か。

    **凍結済みでは足りない**。identity API（candidate hash / 完全比較）は計算の
    ために未凍結の入力をその場で凍らせるので、「凍結済み」を条件にすると、
    identity を 1 回取っただけの精錬中の値が solver へ流れ込める
    （`core/semantic_lifecycle.py`）。

    判定は `isinstance` で行う。`hasattr` で属性を探ると、renderer に渡された
    Ghidra object（記録再生中は proxy）に対して観測が走ってしまい、記録済みの
    観測列に無い問い合わせを作ってしまう。対象は `Expression` だけで、それ以外
    （mock / 文字列 / Ghidra object）はこの判定の外。
    """

    global _EXPRESSION_TYPE, _CONDITION_TYPE
    if _EXPRESSION_TYPE is None:
        from scripts.function_tracer_pcode.core.condition import Condition
        from scripts.function_tracer_pcode.core.expression import Expression

        _EXPRESSION_TYPE = Expression
        _CONDITION_TYPE = Condition
    if not isinstance(expr, (_EXPRESSION_TYPE, _CONDITION_TYPE)):
        return True
    return state_of(expr.__dict__) is SemanticLifecycle.PUBLISHED


def expression_returns_bool(expr) -> bool:
    """式が SMT 上で Bool sort を返すか判定する。"""
    if expr is None:
        return False
    return evaluate_attribute(expr, _node_returns_bool, attribute_cache("returns_bool"))


def _node_returns_bool(expr, child) -> bool:
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.BINARY_OP:
        return expr.operator in _BOOLEAN_BINARY_OPERATORS

    if expr_type == expr_kind.UNARY_OP:
        return expr.operator in {"BOOL_NEGATE", "FLOAT_NAN"}

    if expr_type == expr_kind.PHI:
        branches = expr.value or []
        return bool(branches) and all(
            branch_value is not None and child(branch_value)
            for _, branch_value in branches
        )

    return False


def normalize_call_symbol_name(name: Optional[str]) -> str:
    """CALL 名を SMT-LIB で安全な識別子に変換する。"""
    raw_name = str(name or "call")
    if _SMT_IDENTIFIER_RE.fullmatch(raw_name):
        return f"call_{raw_name}"
    digest = hashlib.sha1(raw_name.encode("utf-8")).hexdigest()[:16]
    return f"call_{digest}_{len(raw_name)}"


def expression_contains_signed_comparison(expr) -> bool:
    """式木のどこかに signed 比較が含まれるか判定する。

    走査は distinct node 1 回ずつ（`iter_expression_nodes`）。共有部分式を
    親ごとに数え直すと、DAG では node 数に対して指数になる。

    PHI の branch 条件は `Condition` でも式そのものでも辿る（描画側が両方を
    描くので、片方だけ見ると符号比較を取り逃す）。
    """

    if expr is None:
        return False
    return any_node(expr, _node_is_signed_comparison, include_expression_conditions=True)


def _node_is_signed_comparison(node) -> bool:
    expr_type = getattr(node, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_type is None or expr_kind is None:
        return False
    return (
        expr_type == expr_kind.BINARY_OP
        and getattr(node, "operator", None) in _SIGNED_COMPARISON_OPERATORS
    )


def expression_node_has_unsupported_smt_ops(
    expr, *, allow_call: bool = False,
) -> bool:
    """Return whether one node lacks an exact SMT lowering.

    Direct operands are retained so local arity, width, and precision
    invariants can be checked. Descendants are deliberately not traversed.
    """
    if expr is None:
        return False

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CALL and not allow_call:
        return True

    if expr_type == expr_kind.BINARY_OP:
        if expr.operator not in _SUPPORTED_BINARY_OPERATORS:
            return True
        if expr.operator in {"PIECE", "SUBPIECE"}:
            return _piece_subpiece_width_issue(expr) is not None
        if expr.operator in _FLOAT_ARITHMETIC_FP_SPECS:
            operands = getattr(expr, "operands", None) or []
            if len(operands) == 2 and any(
                _is_float_rendered_expr(operand) for operand in operands
            ):
                left_bits = expression_smt_bit_width(operands[0])
                right_bits = expression_smt_bit_width(operands[1])
                result_bits = expression_smt_bit_width(expr)
                if not (
                    left_bits == right_bits == result_bits
                    and result_bits in _FLOAT_BV_WIDTH_TO_SORT
                ):
                    return True

    if expr_type == expr_kind.UNARY_OP:
        if expr.operator not in _SUPPORTED_UNARY_OPERATORS:
            return True
        if expr.operator in {"INT_ZEXT", "INT_SEXT"} and int(expr.size or 0) <= 0:
            return True
        if expr.operator == "INT2FLOAT":
            operands = getattr(expr, "operands", None) or []
            operand_bits = (
                expression_smt_bit_width(operands[0])
                if len(operands) == 1
                else 0
            )
            result_bits = int(expr.size or 0) * 8
            if operand_bits <= 0 or result_bits not in _FLOAT_BV_WIDTH_TO_SORT:
                return True

    if expr_type == expr_kind.INTRINSIC:
        if not is_supported_pcode_intrinsic(
            opcode=getattr(expr, "opcode", None),
            mnemonic=getattr(expr, "name", None),
        ):
            return True
        if getattr(expr, "name", None) == "NEON_ext" and not _neon_ext_operands_are_smt_supported(expr):
            return True

    return False


def expression_contains_unsupported_smt_ops(expr, *, allow_call: bool = False) -> bool:
    """SMT renderer が直接扱えない演算子を含むか判定する。

    走査は distinct node 1 回ずつ。判定は node ごとに閉じている
    （`expression_node_has_unsupported_smt_ops`）ので、共有を 1 回で済ませても
    答えは変わらない。
    """

    if expr is None:
        return False
    return any_node(
        expr,
        lambda node: expression_node_has_unsupported_smt_ops(node, allow_call=allow_call),
    )


def expression_uses_smt_uf(expr, *, float_mode: str = "fp") -> bool:
    """Return True when expr needs uninterpreted SMT functions."""
    if expr is None:
        return False
    return bool(
        collect_intrinsic_smt_declarations(expr)
        or collect_float_predicate_smt_declarations(expr, float_mode=float_mode)
    )


def smt_logic_name(
    *,
    uses_float_theory: bool = False,
    uses_arrays: bool = False,
    uses_uf: bool = False,
) -> str:
    if uses_float_theory and uses_arrays:
        return "QF_AUFBVFP"
    if uses_float_theory and uses_uf:
        return "QF_UFFPBV"
    if uses_float_theory:
        return "QF_FPBV"
    if uses_arrays:
        return "QF_AUFBV"
    if uses_uf:
        return "QF_UFBV"
    return "QF_BV"


def _coerce_bool_to_bitvec(expr, expr_smt: str, bits: int) -> str:
    """Bool sort の式を 0/1 の bitvector へ変換する。"""
    if bits <= 0 or not expression_returns_bool(expr):
        return expr_smt
    return f"(ite {expr_smt} (_ bv1 {bits}) (_ bv0 {bits}))"


def _coerce_expr_to_bool(expr, expr_smt: str) -> str:
    """Bitvector-shaped boolean operands are normalized before BOOL_* SMT ops."""
    if expression_returns_bool(expr):
        return expr_smt

    expr_type = getattr(expr, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_kind is not None and expr_type == expr_kind.CONSTANT:
        try:
            return "false" if int(getattr(expr, "value", 0) or 0) == 0 else "true"
        except (TypeError, ValueError):
            return "false"

    bits = expression_smt_bit_width(expr)
    if bits <= 0:
        bits = max(1, int(getattr(expr, "size", 0) or 1) * 8)
    return f"(not (= {expr_smt} (_ bv0 {bits})))"


def _is_condition_node(node) -> bool:
    """`Condition`（式 + 反転）か。式 node と描き方が違うので分けて扱う。"""

    return getattr(node, "expr_type", None) is None and hasattr(node, "expression")


class _SmtChildRenderer:
    """node 本体が子を描く唯一の口。

    本体は「どんな文脈で子を描くか」だけを言い、実際の描画は driver が行う。
    直接の再帰呼び出しを残すと、深い式で Python の stack が尽き、共有部分式が
    木として何度も展開される。
    """

    __slots__ = ("_resolve", "_context", "mapping")

    def __init__(self, resolve, context: SmtRenderContext, mapping) -> None:
        self._resolve = resolve
        self._context = context
        self.mapping = mapping

    @property
    def context(self) -> SmtRenderContext:
        return self._context

    def fragment(self) -> FragmentBuilder:
        """自分の分を書く口（driver 所有）。

        幅が子の数に比例する node はここを通す。後ろから積み直すと文字列 copy
        が幅の 2 乗になる。予算とは関係しない（C2 / performance）。
        """

        return self._resolve.fragment()

    def __call__(
        self,
        node,
        *,
        prefer_signed_arithmetic=None,
        address_context=None,
    ) -> str:
        return self._resolve(
            node,
            self._context.derive(
                prefer_signed_arithmetic=prefer_signed_arithmetic,
                address_context=address_context,
            ),
        )


class _DetachedChildRenderer:
    """driver の外から子を描く口（test や helper の単体利用向け）。

    `_SmtChildRenderer` と同じ呼び方だが、1 回ごとに独立した反復 driver を
    起こす。共有は driver をまたがないので `let` が減るだけで、意味は変わらない。
    **再帰する renderer へは戻らない**（無制限の再帰 fallback を作らない）。
    """

    __slots__ = ("_base", "mapping", "_shared")

    def __init__(
        self,
        *,
        prefer_signed_arithmetic=False,
        symbol_name_mapping=None,
        address_context=False,
        float_mode: str = "uf",
        shared: bool = True,
    ) -> None:
        self._base = build_smt_render_context(
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            address_context=address_context,
            float_mode=float_mode,
            symbol_name_mapping=symbol_name_mapping,
        )
        self.mapping = symbol_name_mapping
        self._shared = shared

    @property
    def context(self) -> SmtRenderContext:
        return self._base

    def fragment(self):
        """driver の外では開けない（組み立ては driver が持つ計画の一部）。

        素通りさせるより、そういう経路を作った時点で止める（今は本体がこの口
        から呼ばれることは無い）。
        """

        raise RenderPlanInvariantError(
            "a node body asked for a fragment builder outside the render driver; "
            "render through render_smt_term"
        )

    def __call__(
        self,
        node,
        *,
        prefer_signed_arithmetic=None,
        address_context=None,
    ) -> str:
        context = self._base.derive(
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            address_context=address_context,
        )
        text = render_smt_term(node, context, self.mapping, shared=self._shared)
        # driver の外で描いても、返す項は型付きでなければならない。素の文字列を
        # 返すと、受け取った側の型付き観測が「性質が無い」で落ちる（そこで文字を
        # 見る後退を許すと、共有の有無で判定が変わる経路が復活する）。
        return RenderedTerm(text, classify_smt_fragment(text, None, False))


def _detached_child_renderer(**kwargs) -> _DetachedChildRenderer:
    return _DetachedChildRenderer(**kwargs)


class SmtTermProperties(NamedTuple):
    """子の描画結果について、**下流の分岐が見てよい**性質。

    描画 text を見る代わりにこれを見る。参照が名前になっても展開されても値は
    変わらないので、共有の有無で判定が動かない。新しい「描画結果を見る分岐」が
    要るときは field を 1 つ足し、`classify_smt_fragment` に 1 行足す。
    """

    #: 既に FP 理論の項として描かれているか（`_normalize_to_fp_expr` が見る）
    is_fp_term: bool = False
    #: 恒真 / 恒偽の literal なら True / False、そうでなければ None（PHI が見る）
    boolean_literal: Optional[bool] = None


def classify_smt_fragment(fragment: str, head, exact: bool) -> SmtTermProperties:
    """fragment から型付きの性質を 1 回だけ決める（**この関数だけが text を見る**）。

    展開後のテキストの先頭は、fragment の先頭が子ならその子の展開の先頭になる。
    だから接頭辞で決まる `is_fp_term` は子から継ぎ、テキスト全体が literal かは
    「fragment が子の参照ちょうど」で決まる。近似ではなく等値。
    """

    if head is not None:
        return SmtTermProperties(
            is_fp_term=head.is_fp_term,
            boolean_literal=head.boolean_literal if exact else None,
        )
    literal = True if fragment == "true" else False if fragment == "false" else None
    return SmtTermProperties(
        is_fp_term=_looks_like_fp_expr(fragment),
        boolean_literal=literal,
    )


def term_is_fp_rendered(term) -> bool:
    """項が既に FP 理論の項として描かれているか。性質が無ければ fail-closed。"""

    return bool(term_properties(term).is_fp_term)


def term_boolean_literal(term) -> Optional[bool]:
    """項が恒真 / 恒偽の literal か。性質が無ければ fail-closed。"""

    return term_properties(term).boolean_literal


def smt_term(text: str, *, is_fp_term: bool = False, boolean_literal=None) -> RenderedTerm:
    """driver の外で型付きの項を作る（detached renderer と test 用）。"""

    return RenderedTerm(
        text,
        SmtTermProperties(is_fp_term=is_fp_term, boolean_literal=boolean_literal),
    )


def render_smt_term(
    root,
    context: SmtRenderContext,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    *,
    shared: bool = True,
    limit_bytes: Optional[int] = None,
) -> str:
    """DAG を 1 回だけ辿って SMT 項を書く（renderer の本体入口）。

    走査は 1 回だけで、node 本体が作るのは自分の分と子の参照（fragment）。木への
    展開は `CountingWriter` へ流しながら行うので、予算に達した時点で書き出しを
    止める（= 完成した出力文字列を作らない）。共有部分式は `let` で 1 回だけ定義する。束縛が 0 個なら出力は
    展開したものと同じ文字列になるので、小さい式の観測可能な text は変わらない。
    """

    counters = RenderCounters(render_invocations=1)

    def body(node, node_context, resolve):
        return _render_smt_node(
            node,
            node_context,
            _SmtChildRenderer(resolve, node_context, symbol_name_mapping),
        )

    policy = SMT_SHARING_POLICY if shared else NO_SHARING_POLICY
    with render_attribute_scope():
        try:
            plan = build_render_plan(
                root,
                context,
                body=body,
                classify=classify_smt_fragment,
                policy=policy,
                counters=counters,
            )
        except RenderGraphCycleError:
            # 閉路を「受け入れない」と決めるのは走査 owner。ここは進めないと
            # 言うだけで、種別の判定を renderer 側に増やさない。
            traverse_semantic_graph(root)
            raise
        names = (
            assign_binding_names(plan, smt_binding_namespace(plan))
            if plan.bound_order
            else {}
        )
        check_plan_invariants(plan, names)
        counters.case_count += _phi_case_count(plan)
        writer = CountingWriter(limit_bytes=limit_bytes, site="core.render_smt.emit")
        write_let_term(writer, plan, names)
        text = writer.getvalue()
    counters.emitted_bytes = writer.emitted_bytes
    record_render(counters)
    return text


def _phi_case_count(plan) -> int:
    """描いた PHI branch（case）の数。

    node 本体の中で数えると、子の解決による再実行の回数だけ水増しされる。
    counter は診断用なので、数えるのは「何を描いたか」が確定してから。
    """

    total = 0
    for instance in plan.instances:
        node = instance.node
        expr_type = getattr(node, "expr_type", None)
        if expr_type is None:
            continue
        if expr_type == expr_type.__class__.PHI:
            total += len(getattr(node, "value", None) or ())
    return total


def _to_smt_internal(
    expr,
    prefer_signed_arithmetic: bool = False,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    address_context: bool = False,
    float_mode: str = "uf",
    *,
    shared: bool = True,
    limit_bytes: Optional[int] = None,
) -> str:
    """描画の内部入口。**反復**で DAG を 1 回だけ辿る。

    引数の並びは従来どおり（呼び出し側は変わらない）。再帰は driver が持つ
    明示 stack へ移したので、深い式でも Python の再帰制限に当たらない。
    """

    context = build_smt_render_context(
        prefer_signed_arithmetic=prefer_signed_arithmetic,
        address_context=address_context,
        float_mode=float_mode,
        symbol_name_mapping=symbol_name_mapping,
    )
    return render_smt_term(
        expr,
        context,
        symbol_name_mapping,
        shared=shared,
        limit_bytes=limit_bytes,
    )


def _render_smt_node(node, context: SmtRenderContext, render_child) -> str:
    """1 つの描画 instance の本体。子は `render_child` 経由でしか描かない。

    本体は counter を持たない。子の解決のたびに同じ本体をもう一度走らせるので、
    ここで数えると再実行の回数だけ水増しされる（数えるのは計画が確定してから）。
    """

    if _is_condition_node(node):
        return _render_condition_node(node, context, render_child)
    return _render_expression_node(node, context, render_child)


def _render_condition_node(condition, context: SmtRenderContext, render_child) -> str:
    expression = getattr(condition, "expression", None)
    expr_smt = render_child(expression)
    expr_smt = _coerce_expr_to_bool(expression, expr_smt)
    if getattr(condition, "negated", False):
        return f"(not {expr_smt})"
    return expr_smt


def _render_expression_node(expr, context: SmtRenderContext, render_child) -> str:
    prefer_signed_arithmetic = context.prefer_signed_arithmetic
    address_context = context.address_context
    float_mode = context.float_mode
    symbol_name_mapping = render_child.mapping

    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CONSTANT:
        bits = expr.get_bit_width()
        global_address = global_address_smt(expr, bits)
        if global_address is not None:
            # The absolute address of a named global differs between the two
            # binaries; the shared symbolic base address is the identity.
            return global_address
        value = expr.value
        if value < 0:
            value = value & ((1 << bits) - 1)
        return f"(_ bv{value} {bits})"

    if expr_type == expr_kind.PARAMETER:
        name = expr.name if expr.name else f"param_{expr.value}"
        if symbol_name_mapping is None:
            return name
        return symbol_name_mapping.get(name, name)

    if expr_type == expr_kind.VARIABLE:
        if address_context:
            projection = semantic_projection(expr)
            if projection.is_address_value_ref and projection.address_offset is not None:
                bits = max(1, expression_smt_bit_width(expr))
                global_address = global_address_smt(expr, bits)
                if global_address is not None:
                    return global_address
                return f"(_ bv{projection.address_offset} {bits})"
        name = expr.name if expr.name else "var"
        if symbol_name_mapping is None:
            return name
        return symbol_name_mapping.get(name, name)

    if expr_type == expr_kind.UNKNOWN:
        return _unknown_smt_symbol_name(expr)

    if expr_type == expr_kind.INTRINSIC:
        return _lower_intrinsic_to_smt(
            expr,
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
            float_mode=float_mode,
            render_child=render_child,
        )

    if expr_type == expr_kind.BINARY_OP:
        operator = getattr(expr, "operator", None)
        operands = tuple(getattr(expr, "operands", None) or ())

        if operator in {"PIECE", "SUBPIECE"}:
            (
                width_issue,
                left_bits,
                right_bits,
                result_bits,
                byte_offset,
            ) = _piece_subpiece_contract(expr)
            if width_issue is not None:
                raise UnsupportedSmtOperatorError(
                    operator=operator,
                    reason=width_issue,
                    operand_bits=max(left_bits, right_bits),
                    result_bits=result_bits,
                )
            # The contract has already checked arity and normalized every
            # value used below, so these accesses cannot escape as raw index
            # or conversion errors.
            left, right = operands

            if operator == "PIECE":
                left_smt = render_child(left)
                right_smt = render_child(right)
                left_smt = _coerce_expr_to_bitvec_width(
                    left, left_smt, left_bits, float_mode=float_mode
                )
                right_smt = _coerce_expr_to_bitvec_width(
                    right, right_smt, right_bits, float_mode=float_mode
                )
                return f"(concat {left_smt} {right_smt})"

            source_smt = render_child(left)
            source_smt = _coerce_expr_to_bitvec_width(
                left, source_smt, left_bits, float_mode=float_mode
            )
            low_bit = byte_offset * 8
            high_bit = low_bit + result_bits - 1
            return f"((_ extract {high_bit} {low_bit}) {source_smt})"

        # Other binary operators retain their existing lowering path. Their
        # arity contract is unrelated to the PIECE/SUBPIECE bit-vector gate.
        left = operands[0]
        right = operands[1]

        left_bits = expression_smt_bit_width(left)
        right_bits = expression_smt_bit_width(right)

        if expr.operator in [
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "INT_LESS",
            "INT_SLESS",
            "INT_LESSEQUAL",
            "INT_SLESSEQUAL",
        ]:
            # 比較の被演算子は符号拡張の好みを引き継がない（従来どおり）。
            # 先に分岐を決めてから子を描くので、同じ子を 2 つの文脈で描いて
            # 片方を捨てる、ということが起きない。
            prefer_sign_extension = expr.operator in _SIGNED_COMPARISON_OPERATORS
            left_is_bool = expression_returns_bool(left)
            right_is_bool = expression_returns_bool(right)
            left_smt = render_child(left, prefer_signed_arithmetic=False)
            right_smt = render_child(right, prefer_signed_arithmetic=False)

            # Bool sort を含む比較は、そのまま zero/sign-extend すると
            # SMT 上で sort error になる。bitvector 比較が必要な場合のみ
            # 0/1 へ変換してから幅を揃える。
            if left_is_bool or right_is_bool:
                should_compare_as_bool = (
                    left_is_bool
                    and right_is_bool
                    and expr.operator in {"INT_EQUAL", "INT_NOTEQUAL"}
                )
                if not should_compare_as_bool:
                    target_bits = max(left_bits, right_bits, 1)
                    left_smt = _coerce_expr_to_bitvec_width(
                        left,
                        left_smt,
                        target_bits,
                        prefer_sign_extension=prefer_sign_extension,
                        float_mode=float_mode,
                    )
                    right_smt = _coerce_expr_to_bitvec_width(
                        right,
                        right_smt,
                        target_bits,
                        prefer_sign_extension=prefer_sign_extension,
                        float_mode=float_mode,
                    )
            elif left_bits != right_bits:
                target_bits = max(left_bits, right_bits)
                if left_bits < target_bits:
                    op = "sign_extend" if prefer_sign_extension else "zero_extend"
                    left_smt = f"((_ {op} {target_bits - left_bits}) {left_smt})"
                if right_bits < target_bits:
                    op = "sign_extend" if prefer_sign_extension else "zero_extend"
                    right_smt = f"((_ {op} {target_bits - right_bits}) {right_smt})"
            op = expr._get_smt_operator(expr.operator)
            return f"({op} {left_smt} {right_smt})"

        left_smt = render_child(left)
        right_smt = render_child(right)

        if (
            float_mode == "fp"
            and expr.operator in _FLOAT_PREDICATE_SMT_NAMES
            and _float_predicate_can_use_fp_theory(expr, left_bits, right_bits)
        ):
            return _float_predicate_to_smt(
                expr.operator,
                left_smt,
                right_smt,
                left,
                right,
                left_bits,
                float_mode=float_mode,
            )

        if expr.operator in _FLOAT_ARITHMETIC_SMT_NAMES:
            float_arith_smt = _float_binary_to_smt(
                expr.operator,
                left,
                right,
                left_smt,
                right_smt,
                left_bits,
                right_bits,
                expression_smt_bit_width(expr) or max(left_bits, right_bits),
                float_mode=float_mode,
            )
            if float_arith_smt is not None:
                return float_arith_smt

        if expr.operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            shift_bits = left_bits
            if right_bits != shift_bits:
                right_smt = _coerce_smt_bitvec_width(right_smt, right_bits, shift_bits)
            op = expr._get_smt_operator(expr.operator)
            shifted_smt = f"({op} {left_smt} {right_smt})"
            return _coerce_smt_bitvec_width(
                shifted_smt,
                shift_bits,
                expression_smt_bit_width(expr) or shift_bits,
            )

        if expr.operator in _ARITHMETIC_BINARY_OPERATORS:
            left_smt = _coerce_bool_to_bitvec(left, left_smt, left_bits)
            right_smt = _coerce_bool_to_bitvec(right, right_smt, right_bits)
            target_bits = (
                expression_smt_bit_width(expr)
                if expr.operator in _BITWISE_BINARY_OPERATORS
                else _preferred_arithmetic_width(left, right, left_bits, right_bits)
            )
            if left_bits != target_bits or right_bits != target_bits:
                if left_bits < target_bits:
                    left_extend = (
                        "sign_extend"
                        if prefer_signed_arithmetic and _expr_prefers_signed_extension(left)
                        else "zero_extend"
                    )
                    left_smt = f"((_ {left_extend} {target_bits - left_bits}) {left_smt})"
                elif left_bits > target_bits:
                    left_smt = _coerce_expr_to_bitvec_width(
                        left,
                        left_smt,
                        target_bits,
                        prefer_sign_extension=False,
                        float_mode=float_mode,
                    )
                if right_bits < target_bits:
                    right_extend = (
                        "sign_extend"
                        if prefer_signed_arithmetic and _expr_prefers_signed_extension(right)
                        else "zero_extend"
                    )
                    right_smt = f"((_ {right_extend} {target_bits - right_bits}) {right_smt})"
                elif right_bits > target_bits:
                    right_smt = _coerce_expr_to_bitvec_width(
                        right,
                        right_smt,
                        target_bits,
                        prefer_sign_extension=False,
                        float_mode=float_mode,
                    )
            op = expr._get_smt_operator(expr.operator)
            return f"({op} {left_smt} {right_smt})"

        if expr.operator in {"BOOL_AND", "BOOL_OR", "BOOL_XOR"}:
            op = expr._get_smt_operator(expr.operator)
            return (
                f"({op} "
                f"{_coerce_expr_to_bool(left, left_smt)} "
                f"{_coerce_expr_to_bool(right, right_smt)})"
            )

        if expr.operator not in _SUPPORTED_BINARY_OPERATORS:
            raise UnsupportedSmtOperatorError(
                operator=expr.operator,
                reason="unsupported binary operator",
                operand_bits=max(left_bits, right_bits),
                result_bits=expression_smt_bit_width(expr),
            )
        op = expr._get_smt_operator(expr.operator)
        return f"({op} {left_smt} {right_smt})"

    if expr_type == expr_kind.UNARY_OP:
        operand = expr.operands[0]
        operand_smt = render_child(operand)
        operand_bits = expression_smt_bit_width(operand)

        if expr.operator == "INT2FLOAT":
            output_bits = int(expr.size or 0) * 8
            if float_mode != "fp":
                raise UnsupportedSmtOperatorError(
                    operator=expr.operator,
                    reason="exact integer-to-float lowering requires FP theory mode",
                    operand_bits=operand_bits,
                    result_bits=output_bits,
                )
            if operand_bits <= 0:
                raise UnsupportedSmtOperatorError(
                    operator=expr.operator,
                    reason="input integer width is unavailable",
                    operand_bits=operand_bits,
                    result_bits=output_bits,
                )
            fp_sort = _FLOAT_BV_WIDTH_TO_SORT.get(output_bits)
            if fp_sort is None:
                raise UnsupportedSmtOperatorError(
                    operator=expr.operator,
                    reason="output floating-point width is unsupported",
                    operand_bits=operand_bits,
                    result_bits=output_bits,
                )
            ebits, sbits = fp_sort
            return f"((_ to_fp {ebits} {sbits}) RNE {operand_smt})"

        if expr.operator == "INT_ZEXT":
            output_bits = int(expr.size or 0) * 8
            if output_bits <= 0:
                raise UnknownSmtExtensionWidthError(
                    operator=expr.operator,
                    operand_bits=operand_bits,
                )
            if expression_returns_bool(operand):
                return _coerce_bool_to_bitvec(operand, operand_smt, output_bits)
            extend_bits = output_bits - operand_bits
            if extend_bits > 0:
                return f"((_ zero_extend {extend_bits}) {operand_smt})"
            if extend_bits == 0:
                return operand_smt
            return f"((_ extract {output_bits - 1} 0) {operand_smt})"

        if expr.operator == "INT_SEXT":
            output_bits = int(expr.size or 0) * 8
            if output_bits <= 0:
                raise UnknownSmtExtensionWidthError(
                    operator=expr.operator,
                    operand_bits=operand_bits,
                )
            if expression_returns_bool(operand):
                return _coerce_bool_to_bitvec(operand, operand_smt, output_bits)
            extend_bits = output_bits - operand_bits
            if extend_bits > 0:
                return f"((_ sign_extend {extend_bits}) {operand_smt})"
            if extend_bits == 0:
                return operand_smt
            return f"((_ extract {output_bits - 1} 0) {operand_smt})"

        if expr.operator == "INT_NEGATE":
            target_bits = expression_smt_bit_width(expr) or operand_bits
            operand_smt = _coerce_bool_to_bitvec(operand, operand_smt, target_bits)
            return f"(bvnot {operand_smt})"

        if expr.operator == "INT_2COMP":
            target_bits = expression_smt_bit_width(expr) or operand_bits
            operand_smt = _coerce_bool_to_bitvec(operand, operand_smt, target_bits)
            return f"(bvneg {operand_smt})"

        if expr.operator == "BOOL_NEGATE":
            return f"(not {_coerce_expr_to_bool(operand, operand_smt)})"

        fp_unary_predicate_smt = _float_unary_predicate_to_smt(
            expr.operator,
            operand,
            operand_smt,
            operand_bits,
            float_mode=float_mode,
        )
        if fp_unary_predicate_smt is not None:
            return fp_unary_predicate_smt

        fp_unary_value_smt = _float_unary_value_to_smt(
            expr.operator,
            operand,
            operand_smt,
            operand_bits,
            float_mode=float_mode,
        )
        if fp_unary_value_smt is not None:
            return fp_unary_value_smt

        fp_unary_smt = _float_unary_to_bitvec_smt(
            expr.operator,
            _coerce_smt_bitvec_width(
                operand_smt,
                operand_bits,
                expression_smt_bit_width(expr) or operand_bits,
            ),
            expression_smt_bit_width(expr) or operand_bits,
        )
        if fp_unary_smt is not None:
            return fp_unary_smt

        if expr.operator not in _SUPPORTED_UNARY_OPERATORS:
            raise UnsupportedSmtOperatorError(
                operator=expr.operator,
                reason="unsupported unary operator",
                operand_bits=operand_bits,
                result_bits=expression_smt_bit_width(expr),
            )
        op = expr._get_smt_operator(expr.operator)
        return f"({op} {operand_smt})"

    if expr_type == expr_kind.CALL:
        raw_func_name = getattr(expr, "name", None)
        func_name = normalize_call_symbol_name(raw_func_name)
        if symbol_name_mapping is not None:
            func_name = (
                symbol_name_mapping.get(raw_func_name, func_name)
                if raw_func_name is not None
                else func_name
            )
            func_name = symbol_name_mapping.get(func_name, func_name)
        operands = getattr(expr, "operands", None) or ()
        if not operands:
            return f"{func_name}"
        # 引数の数だけ長くなる node なので、前から 1 回で組み立てる。
        # 前から 1 回で組み立てる（後ろから積み直すと幅の 2 乗になる）。
        fragment = render_child.fragment()
        fragment.literal(f"({func_name}")
        for operand in operands:
            fragment.literal(" ").term(render_child(operand))
        return fragment.literal(")").build()

    if expr_type == expr_kind.MEMORY:
        mem_bits = expression_smt_bit_width(expr) or 32
        if mem_bits not in _MEMORY_ARRAY_WIDTHS:
            mem_bits = 32
        addr_expr = expr.operands[0]
        addr_smt = render_child(addr_expr, address_context=True)
        addr_smt = _coerce_expr_to_bitvec_width(
            addr_expr,
            addr_smt,
            64,
            prefer_sign_extension=False,
            float_mode=float_mode,
        )
        return f"(select mem{mem_bits} {addr_smt})"

    if expr_type == expr_kind.PHI:
        branches = expr.value
        if not branches:
            return "undefined"

        phi_returns_bool = expression_returns_bool(expr)
        target_bits = expression_smt_bit_width(expr)
        prefer_sign_extension = expression_contains_signed_comparison(expr)

        def render_branch_value(branch_expr):
            if hasattr(branch_expr, "_to_smt_internal"):
                branch_smt = render_child(
                    branch_expr,
                    prefer_signed_arithmetic=prefer_sign_extension,
                )
            else:
                branch_smt = str(branch_expr)

            if phi_returns_bool or not hasattr(branch_expr, "get_bit_width"):
                return branch_smt

            return _coerce_expr_to_bitvec_width(
                branch_expr,
                branch_smt,
                target_bits,
                prefer_sign_extension=prefer_sign_extension,
                float_mode=float_mode,
            )

        def render_branch_condition(cond):
            if cond is not None and hasattr(cond, "_to_smt_internal"):
                return render_child(
                    cond,
                    prefer_signed_arithmetic=prefer_sign_extension,
                )
            if cond is not None and hasattr(cond, "expression"):
                # 内部の再帰。公開入口（`Condition.to_smt`）へ戻らない。
                # 引数は公開入口と同じだけ渡す（`prefer_sign_extension` /
                # `address_context` は条件の描画に伝播させない）— 伝播させると
                # PHI の branch 条件の描画が変わり、判定が動く。
                return render_child(
                    cond,
                    prefer_signed_arithmetic=False,
                    address_context=False,
                )
            return smt_term("true", boolean_literal=True)

        # branch 数だけ入れ子になる node なので、**前から** 1 段ずつ置く。
        # 後ろから `result = f"(ite … {result})"` で積み直すと、文字列 copy が
        # branch 数の 2 乗になる。
        #
        # 畳み込みの意味は積み直し版と同じ: 恒真の条件が出たらその値が最内に
        # なり、後ろの branch は届かない（積み直し版では最後に処理される
        # 最小 index の恒真条件が result を置き換えるので、前から見て最初の
        # 恒真条件と同じ）。恒偽の条件は段を作らない。
        fragment = render_child.fragment()
        opened = 0
        innermost = None
        for index in range(len(branches) - 1):
            cond, val = branches[index]
            cond_str = render_branch_condition(cond)
            # 恒真 / 恒偽の畳み込みは **型付きの性質**で決める。描画文字列を
            # 見ると、その条件に名前が付いた瞬間に畳み込みが消える。
            literal = term_boolean_literal(cond_str)
            if literal is False:
                continue
            val_str = render_branch_value(val)
            if literal is True:
                innermost = val_str
                break
            fragment.literal("(ite ").term(cond_str).literal(" ").term(val_str).literal(" ")
            opened += 1
        if innermost is None:
            innermost = render_branch_value(branches[-1][1])
        fragment.term(innermost)
        return fragment.repeat(")", opened).build()

    return "unknown"


def get_smt_operator(operator: Optional[str] = None) -> str:
    """P-code オペレータを SMT-LIB 演算子へ変換する。"""
    if operator is None:
        return "unknown"

    op_map = {
        "INT_ADD": "bvadd",
        "INT_SUB": "bvsub",
        "INT_MULT": "bvmul",
        "INT_DIV": "bvudiv",
        "INT_SDIV": "bvsdiv",
        "INT_REM": "bvurem",
        "INT_SREM": "bvsrem",
        "INT_AND": "bvand",
        "INT_OR": "bvor",
        "INT_XOR": "bvxor",
        "INT_LEFT": "bvshl",
        "INT_RIGHT": "bvlshr",
        "INT_SRIGHT": "bvashr",
        "INT_EQUAL": "=",
        "INT_NOTEQUAL": "distinct",
        "INT_LESS": "bvult",
        "INT_SLESS": "bvslt",
        "INT_LESSEQUAL": "bvule",
        "INT_SLESSEQUAL": "bvsle",
        "INT_NEGATE": "bvnot",
        "INT_2COMP": "bvneg",
        "BOOL_NEGATE": "not",
        "BOOL_AND": "and",
        "BOOL_OR": "or",
        "BOOL_XOR": "xor",
    }
    return op_map.get(operator, operator.lower())


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.float_theory import (
    _float_binary_to_smt,
    _float_predicate_can_use_fp_theory,
    _float_predicate_to_smt,
    _float_unary_predicate_to_smt,
    _float_unary_to_bitvec_smt,
    _float_unary_value_to_smt,
    _is_float_rendered_expr,
    _looks_like_fp_expr,
    collect_float_predicate_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.intrinsics import (
    _lower_intrinsic_to_smt,
    collect_intrinsic_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.loop_lowering import (
    _neon_ext_operands_are_smt_supported,
)
from scripts.function_tracer_pcode.core.render_smt.unknowns import (
    global_address_smt,
    _unknown_smt_symbol_name,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    _coerce_expr_to_bitvec_width,
    _coerce_smt_bitvec_width,
    _expr_prefers_signed_extension,
    _piece_subpiece_contract,
    _piece_subpiece_width_issue,
    _preferred_arithmetic_width,
    expression_smt_bit_width,
)
