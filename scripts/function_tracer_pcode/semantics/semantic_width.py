# -*- coding: utf-8 -*-
"""Semantic-width aware expression normalization."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Callable, Dict, Optional, Tuple

from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.core import (
    ComparisonSurface,
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
)
from scripts.function_tracer_pcode.core.storage import (
    coerce_storage_info as _coerce_storage_info,
    storage_identity_key_of as _storage_identity_key,
)
from scripts.function_tracer_pcode.core.render_smt import (
    expression_returns_bool,
    expression_smt_bit_width,
)
from scripts.function_tracer_pcode.core.semantic_freeze import publish_semantic_values
from scripts.function_tracer_pcode.core.analysis import derive_memory_effect_bit_width
from scripts.function_tracer_pcode.semantics.param_semantics import (
    ParameterSemanticHint,
    infer_parameter_semantics_by_identity,
)
from scripts.function_tracer_pcode.semantics.rewrite_contract import (
    COMPARISON_NARROWING_RULES,
    EMPTY_REWRITE_AUTHORIZATION,
    ExtensionKind,
    RewriteAuthorization,
    mark_rewritten_surface,
    rewrite_rule,
)


#: ``SUBPIECE(a op b, 0)`` の下位 N bit は ``low_N(a) op low_N(b)`` に常に等しい
#: （mod 2^N の環準同型）。入力仮定を要らない恒等規則。
RING_TRUNCATING_BINARY_OPS = frozenset(
    {
        "INT_ADD",
        "INT_SUB",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
    }
)
COMPARISON_OPS = frozenset(
    {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_SLESS",
        "INT_LESSEQUAL",
        "INT_SLESSEQUAL",
    }
)
SIGNEDNESS_KINDS = frozenset({"signed", "unsigned"})
RETURN_EXTENSION_SURFACE_CANDIDATE_BITS = (64, 32, 16, 8)
RETURN_VALUE_EXTENSION_OPS = frozenset({"INT_ZEXT", "INT_SEXT"})
RETURN_EXTENSION_SURFACE_SOURCE = "cross_side_return_extension_surface"
RETURN_EXTENSION_SURFACE_COERCION = "equal_width_or_object_proven_extract"
RETURN_EXTENSION_SURFACE_KINDS = frozenset({"INT_ZEXT", "INT_SEXT", "none"})

#: 符号付きの比較の演算子（Issue #298 の後、幅の違う比較の揃えには使わない: 描画は伸ばし方を
#: 推測しない。``core/render_smt/render.py`` の ``_fit_comparison_operands``）。
SIGNED_COMPARISON_OPS = frozenset({"INT_SLESS", "INT_SLESSEQUAL"})


class _ExtensionImage:
    """``operand == ext_kind(narrow)`` が（恒等的に、または premise の下で）成り立つこと。"""

    __slots__ = ("narrow", "bits", "kind")

    def __init__(self, narrow: Expression, bits: int, kind: ExtensionKind):
        self.narrow = narrow
        self.bits = bits
        self.kind = kind


class SemanticWidthNormalizer:
    """Semantic-width 書き換え。適用できるのは ``rewrite_contract.REWRITE_RULES`` の規則だけ。

    書き換えは全部 ``_rewritten(rule, expr)`` を通り、規則名が表に無ければ
    programming error。恒等規則は semantic hint を「どこで試すか」の目安にだけ
    使う。parameter を extension 像として使う規則は ``authorization.grant`` から
    だけ入力仮定を受け取る（最終 ``InputCorrespondence`` が含意したもの）。
    normalizer は自分で入力仮定を作らない。
    """

    def __init__(
        self,
        hints_by_identity: Dict[Tuple[object, ...], ParameterSemanticHint],
        authorization: Optional[RewriteAuthorization] = None,
    ):
        self.hints_by_identity = hints_by_identity
        self.authorization = authorization or EMPTY_REWRITE_AUTHORIZATION
        #: 適用した規則ごとの回数（診断と certificate test 用。判定には使わない）。
        self.applied_rules: Dict[str, int] = {}

    def _rewritten(self, rule_name: str, expr: Expression) -> Expression:
        rewrite_rule(rule_name)
        self.applied_rules[rule_name] = self.applied_rules.get(rule_name, 0) + 1
        return expr

    def rewrite_expression(self, expr: Optional[Expression]) -> Optional[Expression]:
        if expr is None:
            return expr

        if expr.expr_type == ExpressionType.PHI and expr.value:
            changed = False
            branches = []
            for cond, value in expr.value:
                new_cond = None
                if cond is not None:
                    new_cond_expr = self.rewrite_expression(cond.expression)
                    new_cond = Condition(new_cond_expr, cond.negated)
                    changed = changed or (new_cond_expr is not cond.expression)
                new_value = self.rewrite_expression(value)
                changed = changed or (new_value is not value)
                branches.append((new_cond, new_value))
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            rebuilt.data_type = expr.data_type
            rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
            rebuilt.storage_info = expr.storage_info
            rebuilt.read_order_key = expr.read_order_key
            return rebuilt

        operands = getattr(expr, "operands", None) or []
        new_operands = [self.rewrite_expression(operand) for operand in operands]
        changed = any(new is not old for new, old in zip(new_operands, operands))

        candidate = expr
        if changed:
            candidate = Expression(
                expr_type=expr.expr_type,
                value=expr.value,
                operator=expr.operator,
                operands=new_operands,
                size=expr.size,
                name=expr.name,
                data_type=expr.data_type,
                data_type_obj=getattr(expr, "data_type_obj", None),
                opcode=getattr(expr, "opcode", None),
                storage_info=expr.storage_info,
                read_order_key=expr.read_order_key,
                runtime_ref=getattr(expr, "runtime_ref", None),
            )

        normalized = self._apply_rules(candidate)
        return normalized

    def _apply_rules(self, expr: Expression) -> Expression:
        if expr.expr_type == ExpressionType.BINARY_OP:
            if expr.operator == "SUBPIECE":
                collapsed = self._normalize_subpiece(expr)
                if collapsed is not None:
                    return collapsed
            if expr.operator == "INT_AND":
                collapsed = self._normalize_mask(expr)
                if collapsed is not None:
                    return collapsed
            if expr.operator in COMPARISON_OPS:
                collapsed = self._normalize_comparison(expr)
                if collapsed is not None:
                    return collapsed
                widened = self._widen_zero_comparison_constant(expr)
                if widened is not None:
                    return widened
        return expr

    # -- subpiece -----------------------------------------------------------

    def _normalize_subpiece(self, expr: Expression) -> Optional[Expression]:
        if len(expr.operands) != 2:
            return None

        source, offset = expr.operands
        if offset.expr_type != ExpressionType.CONSTANT or int(offset.value) != 0:
            return None

        output_bits = expr.get_bit_width()
        if output_bits <= 0:
            return None

        # rule: subpiece_of_extension
        if (
            source.expr_type == ExpressionType.UNARY_OP
            and source.operator in {"INT_SEXT", "INT_ZEXT"}
            and source.operands
        ):
            operand = source.operands[0]
            if operand.get_bit_width() == output_bits:
                return self._rewritten("subpiece_of_extension", operand)

        if source.expr_type != ExpressionType.BINARY_OP or len(source.operands) != 2:
            return None
        # 除算・剰余の狭めは有効にしない: 恒等式は幅に依らないが、production 幅
        # （64→32）で実 lowering の certificate が得られない（z3 が決着しない）。
        if source.operator not in RING_TRUNCATING_BINARY_OPS:
            return None

        # rule: subpiece_of_ring_operation
        left = self._low_part(source.operands[0], output_bits)
        right = self._low_part(source.operands[1], output_bits)
        if left is None or right is None:
            return None

        rebuilt = Expression.binary_op(source.operator, left, right)
        rebuilt.size = output_bits // 8
        rebuilt.data_type = source.data_type
        return self._rewritten("subpiece_of_ring_operation", rebuilt)

    def _low_part(self, expr: Expression, bits: int) -> Optional[Expression]:
        """``low_bits(expr)`` と恒等的に等しい、より狭い式（見つからなければ None）。"""

        if expr.expr_type == ExpressionType.PARAMETER:
            hint = self._parameter_hint(expr)
            if hint is not None and hint.narrow_bits == bits and expr.get_bit_width() > bits:
                return self._low_bits_expr(expr, bits)
            return None
        if (
            expr.expr_type == ExpressionType.UNARY_OP
            and expr.operator in {"INT_SEXT", "INT_ZEXT"}
            and expr.operands
        ):
            inner = self._match_low_expr(expr.operands[0])
            if inner is not None and inner[1] == bits:
                return inner[0]
        return None

    # -- mask ---------------------------------------------------------------

    def _normalize_mask(self, expr: Expression) -> Optional[Expression]:
        """rule: mask_to_zero_extension — ``p & (2^N - 1)`` (W bit) を ``zext_W(low_N(p))`` へ。

        結果は元と同じ W bit。N bit の extract へ裸で置き換えると親の sort と
        全幅値が変わる（``~(p & 0xffffffff) == 0xffffffff00000000``）。
        """

        if len(expr.operands) != 2:
            return None
        param_expr, const_expr = self._split_mask_expr(expr)
        if param_expr is None or const_expr is None:
            return None
        hint = self._parameter_hint(param_expr)
        if hint is None or hint.signedness != "unsigned":
            return None
        width = param_expr.get_bit_width()
        narrow_bits = hint.narrow_bits
        if not (0 < narrow_bits < width) or expr.get_bit_width() != width:
            return None
        if const_expr.get_bit_width() != width:
            return None
        if (int(const_expr.value) & ((1 << width) - 1)) != (1 << narrow_bits) - 1:
            return None
        rebuilt = Expression.unary_op("INT_ZEXT", self._low_bits_expr(param_expr, narrow_bits))
        rebuilt.size = expr.size
        rebuilt.data_type = expr.data_type
        return self._rewritten("mask_to_zero_extension", rebuilt)

    # -- comparison ---------------------------------------------------------

    def _align_comparison_constant_width(self, expr: Expression) -> Optional[Expression]:
        """rule: comparison_constant_width_alignment — ``a[N] op c[W]``（W > N）の c を N bit へ。

        lowering は ``ext_k(a) op c``（k は比較の符号で決まる）なので、c が ext_k の
        像に入るときに限り ``a op low_N(c)`` と同値。そうでなければ触らない。
        """

        left, right = expr.operands
        if (left.expr_type == ExpressionType.CONSTANT) == (right.expr_type == ExpressionType.CONSTANT):
            return None
        constant, other = (left, right) if left.expr_type == ExpressionType.CONSTANT else (right, left)
        other_bits = other.get_bit_width()
        if other_bits <= 0 or other_bits % 8 or constant.get_bit_width() <= other_bits:
            return None
        if expression_returns_bool(other):
            return None
        # Issue #298: 描画は幅の違う比較を符号で伸ばさない（伸ばし方が値を変えない形だけを揃える）。
        # 揃えも同じ条件に限る: 符号なしの比較（等値・不等・<u・<=u）で、定数が zero・sign どちらの
        # 拡張の像にも入る（狭い幅で最上位 bit が 0）ときだけ ``a op low_N(c)`` と同値
        if expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
            return None
        narrowed = self._narrow_constant(constant, other_bits, ExtensionKind.ZERO)
        if narrowed is None or self._narrow_constant(constant, other_bits, ExtensionKind.SIGN) is None:
            return None
        operands = (narrowed, other) if constant is left else (other, narrowed)
        rebuilt = Expression.binary_op(expr.operator, *operands)
        rebuilt.size = expr.size
        return self._rewritten("comparison_constant_width_alignment", rebuilt)

    def _widen_zero_comparison_constant(self, expr: Expression) -> Optional[Expression]:
        """rule: comparison_zero_constant_width — 比較の定数 0 を相手の幅へ揃える。"""

        if len(expr.operands) != 2:
            return None
        left, right = expr.operands
        # Issue #298: 0 を相手の幅へ **狭める** と、符号付きの順序の比較は相手の伸ばし方（sign）を
        # 決めたことになる。狭める向きは、伸ばし方に依らない比較（符号なし）に限る
        narrowing_allowed = expr.operator not in SIGNED_COMPARISON_OPS
        new_left = _zero_constant_at_peer_width(left, right, narrowing_allowed=narrowing_allowed)
        new_right = _zero_constant_at_peer_width(right, left, narrowing_allowed=narrowing_allowed)
        if new_left is left and new_right is right:
            return None
        return self._rewritten(
            "comparison_zero_constant_width",
            expr.clone_with(operands=[new_left, new_right]),
        )

    def _normalize_comparison(self, expr: Expression) -> Optional[Expression]:
        """演算子を保ったまま両辺を extension 像の狭い値へ置き換える。

        演算子ごとの規則は ``COMPARISON_NARROWING_RULES``、規則が意味を保存する
        ext の種類は rule 表の ``image_kinds``。
        """

        if len(expr.operands) != 2:
            return None
        aligned = self._align_comparison_constant_width(expr)
        if aligned is not None:
            return aligned
        rule_name = COMPARISON_NARROWING_RULES.get(expr.operator)
        if rule_name is None:
            return None
        allowed_kinds = rewrite_rule(rule_name).image_kinds

        left, right = expr.operands
        left_image = self._extension_image(left, rule_name)
        right_image = self._extension_image(right, rule_name)

        if left_image is not None and right.expr_type == ExpressionType.CONSTANT:
            right_image = self._constant_image(right, left, left_image)
        elif right_image is not None and left.expr_type == ExpressionType.CONSTANT:
            left_image = self._constant_image(left, right, right_image)

        if left_image is None or right_image is None:
            return None
        if left_image.kind != right_image.kind or left_image.kind not in allowed_kinds:
            return None
        if left_image.bits != right_image.bits:
            return None
        if left.get_bit_width() != right.get_bit_width():
            return None
        if left_image.bits >= left.get_bit_width():
            return None

        rebuilt = Expression.binary_op(expr.operator, left_image.narrow, right_image.narrow)
        rebuilt.size = expr.size
        return self._rewritten(rule_name, rebuilt)

    def _constant_image(
        self,
        constant: Expression,
        peer: Expression,
        peer_image: _ExtensionImage,
    ) -> Optional[_ExtensionImage]:
        if constant.get_bit_width() != peer.get_bit_width():
            return None
        narrowed = self._narrow_constant(constant, peer_image.bits, peer_image.kind)
        if narrowed is None:
            return None
        return _ExtensionImage(narrowed, peer_image.bits, peer_image.kind)

    # -- operand classification --------------------------------------------

    def _extension_image(self, expr: Expression, rule_name: str) -> Optional[_ExtensionImage]:
        """``expr == ext_kind(narrow)`` を示せる場合だけ返す。

        構文から恒等的に言えるもの（``_syntactic_image``）か、parameter ``p`` に
        ついて規則 ``rule_name`` が最終 relation から ``p == ext(low_N(p))`` を
        受け取れるとき（``authorization.grant``）だけ。hint は使わない。
        """

        image = self._syntactic_image(expr)
        if image is not None:
            return image
        if expr.expr_type == ExpressionType.PARAMETER:
            assumption = self._parameter_grant(expr, rule_name)
            if assumption is None:
                return None
            return _ExtensionImage(
                self._low_bits_expr(expr, assumption.narrow_bits),
                assumption.narrow_bits,
                assumption.kind,
            )
        return None

    def _syntactic_image(self, expr: Expression) -> Optional[_ExtensionImage]:
        """入力仮定無しで ``expr == ext_kind(narrow)`` が成り立つ形。

        * ``SEXT(e)`` / ``ZEXT(e)``（e が既知の狭い値のとき）。
        * ``p & (2^N - 1)``（恒等的に ``zext(low_N(p))``。N は hint から選ぶだけ）。
        """

        if (
            expr.expr_type == ExpressionType.UNARY_OP
            and expr.operator in {"INT_SEXT", "INT_ZEXT"}
            and expr.operands
        ):
            operand = expr.operands[0]
            inner = self._match_low_expr(operand)
            operand_bits = operand.get_bit_width()
            if inner is None or inner[0] is not operand or operand_bits >= expr.get_bit_width():
                return None
            kind = ExtensionKind.SIGN if expr.operator == "INT_SEXT" else ExtensionKind.ZERO
            return _ExtensionImage(operand, operand_bits, kind)

        if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_AND":
            param_expr, const_expr = self._split_mask_expr(expr)
            if param_expr is None or const_expr is None:
                return None
            width = param_expr.get_bit_width()
            hint = self._parameter_hint(param_expr)
            if hint is None or not (0 < hint.narrow_bits < width):
                return None
            if const_expr.get_bit_width() != width or expr.get_bit_width() != width:
                return None
            if (int(const_expr.value) & ((1 << width) - 1)) != (1 << hint.narrow_bits) - 1:
                return None
            return _ExtensionImage(
                self._low_bits_expr(param_expr, hint.narrow_bits),
                hint.narrow_bits,
                ExtensionKind.ZERO,
            )
        return None

    def _match_low_expr(self, expr: Expression) -> Optional[Tuple[Expression, int]]:
        """既存の「狭い値」パターン。返す式は ``expr`` の下位 bits と恒等的に等しい。"""

        if expr.expr_type == ExpressionType.PARAMETER:
            hint = self._parameter_hint(expr)
            bits = expr.get_bit_width()
            if hint is None:
                return (expr, bits) if bits <= 32 else None
            if bits == hint.narrow_bits:
                return (expr, bits)
            if bits > hint.narrow_bits:
                return (self._low_bits_expr(expr, hint.narrow_bits), hint.narrow_bits)
            return None

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "SUBPIECE"
            and len(expr.operands) == 2
        ):
            source, offset = expr.operands
            if offset.expr_type != ExpressionType.CONSTANT or int(offset.value) != 0:
                return None
            bits = expr.get_bit_width()
            if source.expr_type == ExpressionType.PARAMETER:
                hint = self._parameter_hint(source)
                if hint is not None and bits == hint.narrow_bits:
                    return (expr, bits)
            if bits <= 32:
                return (expr, bits)
            return None

        if (
            expr.expr_type == ExpressionType.BINARY_OP
            and expr.operator == "INT_AND"
            and len(expr.operands) == 2
        ):
            image = self._syntactic_image(expr)
            if image is not None:
                return (image.narrow, image.bits)
        return None

    def _parameter_hint(self, expr: Expression) -> Optional[ParameterSemanticHint]:
        if expr.expr_type != ExpressionType.PARAMETER:
            return None
        try:
            index = int(getattr(expr, "value", -1))
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            hint = self.hints_by_identity.get(("parameter_index", index))
            if hint is not None:
                return hint
        storage_key = _storage_identity_key(getattr(expr, "storage_info", None))
        if storage_key is not None:
            return self.hints_by_identity.get(("parameter_storage", storage_key))
        return None

    def _parameter_grant(self, expr: Expression, rule_name: str):
        value = getattr(expr, "value", None)
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            return None
        return self.authorization.grant(rule_name, int(value), expr.get_bit_width())

    def _split_mask_expr(self, expr: Expression):
        left, right = expr.operands
        if left.expr_type == ExpressionType.PARAMETER and right.expr_type == ExpressionType.CONSTANT:
            return left, right
        if right.expr_type == ExpressionType.PARAMETER and left.expr_type == ExpressionType.CONSTANT:
            return right, left
        return None, None

    def _low_bits_expr(self, expr: Expression, narrow_bits: int) -> Expression:
        if expr.get_bit_width() == narrow_bits:
            return expr
        subpiece = Expression.binary_op(
            "SUBPIECE",
            expr,
            Expression.constant(0, size=max(1, expr.size or 1)),
        )
        subpiece.size = max(1, narrow_bits // 8)
        return subpiece

    def _narrow_constant(
        self,
        expr: Expression,
        narrow_bits: int,
        kind: ExtensionKind,
    ) -> Optional[Expression]:
        """定数 ``c`` が ``ext_kind(low_N(c))`` に等しいときだけ ``low_N(c)`` を返す。"""

        if expr.expr_type != ExpressionType.CONSTANT:
            return None

        original_bits = expr.get_bit_width()
        if original_bits <= narrow_bits or narrow_bits <= 0:
            return None
        from scripts.function_tracer_pcode.core.address_provenance import carries_image_address

        if carries_image_address(expr):
            # Issue #282: image の番地の出自を持つ定数は素の数値に作り直さない
            return None

        original_mask = (1 << original_bits) - 1
        narrow_mask = (1 << narrow_bits) - 1
        value_mod = int(expr.value) & original_mask
        low_value = value_mod & narrow_mask

        if kind is ExtensionKind.SIGN and low_value & (1 << (narrow_bits - 1)):
            expected = low_value | (((1 << (original_bits - narrow_bits)) - 1) << narrow_bits)
        else:
            expected = low_value
        if expected != value_mod:
            return None

        narrowed = low_value
        if kind is ExtensionKind.SIGN and low_value & (1 << (narrow_bits - 1)):
            narrowed = low_value - (1 << narrow_bits)
        return Expression.constant(narrowed, size=max(1, narrow_bits // 8))


def _rewritten_expr_bit_width(expr: Any) -> int:
    if expr is None:
        return 0
    try:
        return max(0, int(expression_smt_bit_width(expr) or 0))
    except Exception:
        pass
    get_bit_width = getattr(expr, "get_bit_width", None)
    if callable(get_bit_width):
        try:
            return max(0, int(get_bit_width() or 0))
        except Exception:
            return 0
    return 0


def normalize_analysis_semantic_width(
    analysis: FunctionReturnAnalysis,
    hints: Optional[Dict[int, ParameterSemanticHint]] = None,
    *,
    authorization: Optional[RewriteAuthorization] = None,
) -> FunctionReturnAnalysis:
    """Return a copy of the analysis with semantic-width rewrites applied.

    ``authorization`` は最終 ``InputCorrespondence`` が含意する入力仮定。省略時は
    空（恒等規則だけ）で、これは常に健全。
    """

    source = analysis
    analysis = _synchronize_parameter_expression_metadata(analysis)

    inferred_hints_by_identity = infer_parameter_semantics_by_identity(analysis)
    if hints is None:
        hints_by_identity = inferred_hints_by_identity
    else:
        hints_by_identity = dict(inferred_hints_by_identity)
        hints_by_identity.update(_build_hints_by_object_identity(analysis, hints))

    normalizer = SemanticWidthNormalizer(hints_by_identity, authorization)
    # **この関数の出口が公開点**。`_rewrite_analysis_expressions` は途中段
    # （`_synchronize_parameter_expression_metadata`）でも使う書き換えの「手順」
    # なので、そちらで公開すると、まだ幅を直している最中の値を確定扱いにして
    # しまう。完成を宣言できるのは、書き換えを全部終えたここだけ。
    normalized = publish_semantic_values(
        _rewrite_analysis_expressions(
            analysis,
            normalizer.rewrite_expression,
            simplify_conditions=True,
        )
    )
    # 書き換え結果は raw ではない。最終 relation の producer はこれを拒否する。
    return mark_rewritten_surface(normalized) if normalized is not source else normalized


def align_return_value_extension_surfaces(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
    """Align return comparison surfaces only from cross-side extension evidence."""

    surface_alignment = _common_return_extension_surface_alignment(analysis1, analysis2)
    if surface_alignment is None:
        return analysis1, analysis2
    target_bits, evidence = surface_alignment
    aligned = []
    for analysis in (analysis1, analysis2):
        result = _with_return_extension_surface(analysis, target_bits, evidence)
        aligned.append(mark_rewritten_surface(result) if result is not analysis else result)
    return aligned[0], aligned[1]


def _common_return_extension_surface_alignment(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[int, Dict[str, Any]]]:
    surface1 = analysis1.get_comparison_surface()
    surface2 = analysis2.get_comparison_surface()
    if getattr(surface1, "kind", None) != "return_value" or getattr(surface2, "kind", None) != "return_value":
        return None

    bits1 = _positive_int(getattr(surface1, "explicit_bit_width", None))
    bits2 = _positive_int(getattr(surface2, "explicit_bit_width", None))
    if bits1 is None or bits2 is None:
        return None
    wide_bits = min(bits1, bits2)

    for candidate_bits in RETURN_EXTENSION_SURFACE_CANDIDATE_BITS:
        if candidate_bits > wide_bits or (candidate_bits == wide_bits and bits1 == bits2):
            continue
        profiles1 = _analysis_return_extension_surface_profiles(analysis1, candidate_bits)
        profiles2 = _analysis_return_extension_surface_profiles(analysis2, candidate_bits)
        if profiles1 is None or profiles2 is None:
            continue
        evidence = _return_extension_surface_evidence(candidate_bits, profiles1, profiles2)
        if evidence is not None:
            return candidate_bits, evidence
    return None


def _analysis_return_extension_surface_profiles(
    analysis: FunctionReturnAnalysis,
    candidate_bits: int,
) -> Optional[Tuple[Tuple[str, int], ...]]:
    profiles = []
    for ret in list(getattr(analysis, "returns", None) or []):
        compatible, ret_profiles = _return_expr_supports_extension_surface(
            getattr(ret, "value", None),
            candidate_bits,
        )
        if not compatible:
            return None
        profiles.extend(ret_profiles)
    if not profiles:
        return None
    return tuple(sorted(set(profiles)))


def _return_extension_surface_evidence(
    candidate_bits: int,
    profiles1: Tuple[Tuple[str, int], ...],
    profiles2: Tuple[Tuple[str, int], ...],
) -> Optional[Dict[str, Any]]:
    all_profiles = tuple(sorted(set(tuple(profiles1) + tuple(profiles2))))
    extension_profiles = tuple(profile for profile in all_profiles if profile[0] in RETURN_VALUE_EXTENSION_OPS)
    if not extension_profiles:
        return None
    extension_kinds = tuple(sorted({profile[0] for profile in extension_profiles}))
    if len(extension_kinds) > 1:
        return None
    source_widths = tuple(sorted({int(profile[1]) for profile in extension_profiles}))
    return {
        "source": RETURN_EXTENSION_SURFACE_SOURCE,
        "extension_surface_bit_width": int(candidate_bits),
        "return_width_sign_artifact": True,
        "extension_surface_coercion": RETURN_EXTENSION_SURFACE_COERCION,
        "extension_surface_extension_kind": extension_kinds[0] if extension_kinds else "none",
        "extension_surface_source_bit_widths": source_widths,
    }


def _return_expr_supports_extension_surface(
    expr: Optional[Expression],
    candidate_bits: int,
) -> Tuple[bool, Tuple[Tuple[str, int], ...]]:
    if expr is None:
        return False, ()

    expr_bits = _expression_bit_width(expr)
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        if expr_bits == candidate_bits:
            return True, ()
        return False, ()

    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        profiles = []
        for _condition, value in tuple(getattr(expr, "value", ()) or ()):
            compatible, branch_profiles = _return_expr_supports_extension_surface(value, candidate_bits)
            if not compatible:
                return False, ()
            profiles.extend(branch_profiles)
        return True, tuple(sorted(set(profiles)))

    if getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in RETURN_VALUE_EXTENSION_OPS:
        operands = list(getattr(expr, "operands", None) or [])
        if len(operands) != 1:
            return False, ()
        operand_bits = _expression_bit_width(operands[0])
        if expr_bits >= candidate_bits and 0 < operand_bits <= candidate_bits:
            return True, ((str(getattr(expr, "operator", "")).upper(), int(operand_bits)),)
        return False, ()

    high_zero_piece = _return_piece_zero_extension_profile(expr, candidate_bits)
    if high_zero_piece is not None:
        return True, (high_zero_piece,)

    if expr_bits == candidate_bits:
        return True, (("EXACT_WIDTH", int(candidate_bits)),)
    if 0 < expr_bits < candidate_bits:
        return False, ()

    readonly_evidence = _readonly_reduction_supports_extension_surface(expr, candidate_bits)
    if readonly_evidence is not None:
        return readonly_evidence

    return False, ()


def _return_piece_zero_extension_profile(
    expr: Expression,
    candidate_bits: int,
) -> Optional[Tuple[str, int]]:
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if str(getattr(expr, "operator", "") or "").upper() != "PIECE":
        return None
    operands = list(getattr(expr, "operands", None) or [])
    if len(operands) != 2:
        return None
    high, low = operands
    expr_bits = _expression_bit_width(expr)
    low_bits = _expression_bit_width(low)
    high_bits = _expression_bit_width(high)
    if expr_bits <= candidate_bits or low_bits != candidate_bits or high_bits <= 0:
        return None
    if expr_bits != high_bits + low_bits:
        return None
    if getattr(high, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        high_value = int(getattr(high, "value", None))
    except (TypeError, ValueError):
        return None
    if high_value != 0:
        return None
    return "INT_ZEXT", int(candidate_bits)


def _readonly_reduction_supports_extension_surface(
    expr: Expression,
    candidate_bits: int,
) -> Optional[Tuple[bool, Tuple[Tuple[str, int], ...]]]:
    if getattr(expr, "expr_type", None) != ExpressionType.INTRINSIC:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if not isinstance(runtime_ref, ReadonlyReductionRef):
        return None

    expr_bits = _expression_bit_width(expr)
    if expr_bits == candidate_bits:
        return True, (("READONLY_EXACT_WIDTH", int(candidate_bits)),)
    if expr_bits < candidate_bits:
        return False, ()

    proof = getattr(runtime_ref, "accumulator_proof", None)
    if proof is None:
        return False, ()
    if not bool(getattr(proof, "return_region_value_proven", False)):
        return False, ()
    if not _readonly_reduction_terms_fit_surface(runtime_ref, candidate_bits):
        return False, ()
    profiles = _readonly_reduction_return_extension_profiles(
        runtime_ref,
        candidate_bits,
        target_bits=expr_bits,
    )
    if not profiles:
        return False, ()
    return True, profiles


def _readonly_reduction_terms_fit_surface(
    runtime_ref: ReadonlyReductionRef,
    candidate_bits: int,
) -> bool:
    candidate_size = max(1, candidate_bits // 8)
    proof = getattr(runtime_ref, "accumulator_proof", None)
    owners = (runtime_ref, proof, getattr(runtime_ref, "loop_summary", None))
    for owner in owners:
        if owner is None:
            continue
        for attr_name in ("element_size", "result_size"):
            value = _positive_int(getattr(owner, attr_name, None))
            if value is not None and value <= candidate_size:
                return True
        for attr_name in (
            "seed_terms",
            "lane_terms",
            "loop_body_witnesses",
            "exact_return_witnesses",
            "semantic_witnesses",
            "witnesses",
        ):
            if _readonly_term_container_fits_surface(getattr(owner, attr_name, None), candidate_size):
                return True
    return False


def _readonly_term_container_fits_surface(value: Any, candidate_size: int) -> bool:
    saw_term = False
    for item in tuple(value or ()):
        access_size = _positive_int(getattr(item, "access_size", None))
        if access_size is not None:
            if access_size > candidate_size:
                return False
            saw_term = True
            continue
        if isinstance(item, tuple) and len(item) >= 2:
            tuple_size = _positive_int(item[1])
            if tuple_size is not None:
                if tuple_size > candidate_size:
                    return False
                saw_term = True
                continue
        terms = getattr(item, "terms", None)
        if terms is not None:
            nested_items = tuple(terms or ())
            if not nested_items:
                continue
            if not _readonly_term_container_fits_surface(nested_items, candidate_size):
                return False
            saw_term = True
    return saw_term


def _readonly_reduction_return_extension_profiles(
    runtime_ref: ReadonlyReductionRef,
    candidate_bits: int,
    *,
    target_bits: int,
) -> Tuple[Tuple[str, int], ...]:
    profiles = []
    proof = getattr(runtime_ref, "accumulator_proof", None)
    for owner in (proof, getattr(runtime_ref, "loop_summary", None), runtime_ref):
        for op_ref in tuple(getattr(owner, "return_value_op_refs", ()) or ()):
            profile = _readonly_return_extension_profile_from_op_ref(
                op_ref,
                candidate_bits,
                target_bits=target_bits,
            )
            if profile is not None:
                profiles.append(profile)
    return tuple(sorted(set(profiles)))


def _readonly_return_extension_profile_from_op_ref(
    op_ref: Any,
    candidate_bits: int,
    *,
    target_bits: int,
) -> Optional[Tuple[str, int]]:
    mnemonic = str(getattr(op_ref, "mnemonic", "") or "").upper()
    if mnemonic not in RETURN_VALUE_EXTENSION_OPS:
        return None
    input_size_fn = getattr(op_ref, "input_size", None)
    if callable(input_size_fn):
        source_size = _positive_int(input_size_fn(0))
    else:
        input_sizes = tuple(getattr(op_ref, "input_sizes", ()) or ())
        source_size = _positive_int(input_sizes[0]) if input_sizes else None
    if source_size is None:
        return None
    source_bits = int(source_size) * 8
    if source_bits != int(candidate_bits):
        return None
    output_size = _positive_int(getattr(op_ref, "output_size", None))
    if output_size is None:
        return None
    output_bits = int(output_size) * 8
    if output_bits <= source_bits:
        return None
    if int(target_bits or 0) > 0 and output_bits < int(target_bits):
        return None
    return mnemonic, source_bits


def _with_return_extension_surface(
    analysis: FunctionReturnAnalysis,
    target_bits: int,
    alignment_evidence: Dict[str, Any],
) -> FunctionReturnAnalysis:
    surface = analysis.get_comparison_surface()
    old_bits = _positive_int(getattr(surface, "explicit_bit_width", None))
    if old_bits == target_bits:
        return analysis

    evidence = dict(getattr(surface, "evidence", None) or {})
    evidence.update(alignment_evidence)
    evidence.update(
        {
            "declared_bit_width": old_bits,
            "extension_surface_bit_width": target_bits,
        }
    )
    return replace(
        analysis,
        comparison_surface=ComparisonSurface(
            kind="return_value",
            explicit_bit_width=target_bits,
            type_name=getattr(surface, "type_name", None),
            type_obj=getattr(surface, "type_obj", None),
            use_sign_extension=False,
            evidence=evidence,
        ),
    )


def _positive_int(value: Any) -> Optional[int]:
    try:
        int_value = int(value)
    except (TypeError, ValueError):
        return None
    return int_value if int_value > 0 else None


def _expression_bit_width(expr: Optional[Expression]) -> int:
    if expr is None:
        return 0
    try:
        return max(0, int(expression_smt_bit_width(expr) or 0))
    except Exception:
        pass
    get_bit_width = getattr(expr, "get_bit_width", None)
    if callable(get_bit_width):
        try:
            return max(0, int(get_bit_width() or 0))
        except Exception:
            return 0
    return 0


def parameter_metadata_synchronizer(parameters: Any) -> Callable[[Optional[Expression]], Optional[Expression]]:
    """PARAMETER leaf の index・型・幅を parameter 表の descriptor に揃える書き換え。

    意味は変えない前提の metadata 同期で、leaf は descriptor の parameter symbol
    として描かれる。宣言と幅の違う leaf は同期で幅の情報を失うので、最終 relation の
    closure 走査（``projection_closure``）がその leaf を hidden input として数え、
    relation を不十分にする（Issue #167）。この同期の owner はここだけ。
    """

    params_by_index: Dict[int, Dict[str, Any]] = {}
    params_by_storage_candidates: Dict[Tuple[object, ...], list[Dict[str, Any]]] = {}
    for param in list(parameters or []):
        descriptor = dict(param or {})
        index = descriptor.get("index")
        if isinstance(index, int) and index >= 0:
            params_by_index[index] = descriptor
        storage_key = _storage_identity_key(descriptor.get("storage_info", descriptor.get("storage")))
        if storage_key is not None:
            params_by_storage_candidates.setdefault(storage_key, []).append(descriptor)
    params_by_storage = {
        storage_key: descriptors[0]
        for storage_key, descriptors in params_by_storage_candidates.items()
        if len(descriptors) == 1
    }
    return lambda expr: _rewrite_parameter_expression_metadata(expr, params_by_index, params_by_storage)


def _synchronize_parameter_expression_metadata(
    analysis: FunctionReturnAnalysis,
) -> FunctionReturnAnalysis:
    parameters = list(analysis.parameters or [])
    if not parameters:
        return analysis
    return _rewrite_analysis_expressions(
        analysis,
        parameter_metadata_synchronizer(parameters),
        simplify_conditions=False,
    )


def _rewrite_analysis_expressions(
    analysis: FunctionReturnAnalysis,
    rewrite_expr,
    *,
    simplify_conditions: bool,
) -> FunctionReturnAnalysis:
    changed = False
    rewritten_returns = []
    for ret in analysis.returns:
        new_value = rewrite_expr(ret.value)
        new_conditions, conditions_changed = _rewrite_conditions(
            ret.conditions,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if new_value is not ret.value or conditions_changed:
            changed = True
        rewritten_returns.append(
            replace(
                ret,
                value=new_value,
                conditions=new_conditions,
            )
        )

    rewritten_return_outcomes = []
    for outcome in getattr(analysis, "return_outcomes", ()) or ():
        new_value = rewrite_expr(outcome.value)
        new_guard, guard_changed = _rewrite_conditions(
            outcome.guard,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        new_return_info = outcome.return_info
        if new_return_info is not None:
            info_value = rewrite_expr(new_return_info.value)
            info_conditions, info_conditions_changed = _rewrite_conditions(
                new_return_info.conditions,
                rewrite_expr,
                simplify=simplify_conditions,
            )
            if info_value is not new_return_info.value or info_conditions_changed:
                new_return_info = replace(
                    new_return_info,
                    value=info_value,
                    conditions=info_conditions,
                )
                changed = True
        if new_value is not outcome.value or guard_changed:
            changed = True
        rewritten_return_outcomes.append(
            replace(
                outcome,
                value=new_value,
                guard=tuple(new_guard),
                return_info=new_return_info,
            )
        )

    rewritten_divergence_outcomes = []
    for outcome in getattr(analysis, "divergence_outcomes", ()) or ():
        new_guard, guard_changed = _rewrite_conditions(
            outcome.guard,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if guard_changed:
            changed = True
        rewritten_divergence_outcomes.append(replace(outcome, guard=tuple(new_guard)))

    rewritten_unknown_outcomes = []
    for outcome in getattr(analysis, "unknown_outcomes", ()) or ():
        new_guard, guard_changed = _rewrite_conditions(
            outcome.guard,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if guard_changed:
            changed = True
        rewritten_unknown_outcomes.append(replace(outcome, guard=tuple(new_guard)))

    rewritten_effect_summary = _rewrite_effect_summary_expressions(
        getattr(analysis, "effect_summary", None),
        rewrite_expr,
        simplify_conditions=simplify_conditions,
    )
    if rewritten_effect_summary is not getattr(analysis, "effect_summary", None):
        changed = True

    rewritten_comparison_surface = getattr(analysis, "comparison_surface", None)
    if rewritten_comparison_surface is not None and rewritten_comparison_surface.kind == "memory_effect":
        # The surface width follows the rewritten comparison values (the
        # returns), which for a void function is the synthetic effect
        # expression and for stores ⊕ return value the wider combined
        # expression; see FunctionReturnAnalysis.memory_effect_surface_bit_width.
        explicit_bits = derive_memory_effect_bit_width(
            rewritten_returns, rewritten_effect_summary, _rewritten_expr_bit_width
        )
        if explicit_bits > 0 and explicit_bits != rewritten_comparison_surface.explicit_bit_width:
            changed = True
            rewritten_comparison_surface = replace(
                rewritten_comparison_surface,
                explicit_bit_width=explicit_bits,
            )

    if not changed:
        return analysis

    return replace(
        analysis,
        returns=rewritten_returns,
        return_outcomes=tuple(rewritten_return_outcomes),
        divergence_outcomes=tuple(rewritten_divergence_outcomes),
        unknown_outcomes=tuple(rewritten_unknown_outcomes),
        effect_summary=rewritten_effect_summary,
        comparison_surface=rewritten_comparison_surface,
    )

def _rewrite_conditions(
    conditions,
    rewrite_expr,
    *,
    simplify: bool,
):
    rewritten = []
    for cond in conditions or []:
        rewritten.append(Condition(rewrite_expr(cond.expression), cond.negated))
    if simplify:
        rewritten = ConditionSimplifier.simplify_conditions(rewritten)

    original = list(conditions or [])
    if len(rewritten) != len(original):
        changed = True
    else:
        changed = any(
            new.expression is not old.expression or new.negated != old.negated
            for new, old in zip(rewritten, original)
        )
    return rewritten, changed


def _zero_constant_at_peer_width(
    candidate: Expression, peer: Expression, *, narrowing_allowed: bool = True,
) -> Expression:
    """比較の operand が定数 0 なら相手の幅の 0（そうでなければそのまま）。

    ``narrowing_allowed`` が偽なら、相手が定数より狭いときは揃えない（伸ばし方を決めない）。
    """

    if candidate is None or peer is None or candidate.expr_type != ExpressionType.CONSTANT:
        return candidate
    try:
        if int(candidate.value) != 0:
            return candidate
    except (TypeError, ValueError):
        return candidate
    peer_size = int(getattr(peer, "size", 0) or 0)
    if peer_size > 0:
        desired_size = peer_size
    else:
        peer_bits = _expression_bit_width(peer)
        if peer_bits <= 0 or peer_bits % 8 != 0:
            return candidate
        desired_size = max(1, peer_bits // 8)
    current_size = int(getattr(candidate, "size", 0) or 0)
    if current_size == desired_size:
        return candidate
    if not narrowing_allowed and current_size > desired_size:
        return candidate
    return candidate.clone_with(size=desired_size)


def _rewrite_effect_summary_expressions(
    effect_summary,
    rewrite_expr,
    *,
    simplify_conditions: bool,
):
    if effect_summary is None:
        return None

    changed = False
    rewritten_effects = []
    for effect in getattr(effect_summary, "effects", []) or []:
        new_value = rewrite_expr(effect.value)
        new_conditions, conditions_changed = _rewrite_conditions(
            effect.conditions,
            rewrite_expr,
            simplify=simplify_conditions,
        )
        if new_value is not effect.value or conditions_changed:
            changed = True
        rewritten_effects.append(
            replace(
                effect,
                value=new_value,
                conditions=new_conditions,
            )
        )

    new_synthetic_expr = rewrite_expr(getattr(effect_summary, "synthetic_expr", None))
    if new_synthetic_expr is not getattr(effect_summary, "synthetic_expr", None):
        changed = True

    if not changed:
        return effect_summary

    return replace(
        effect_summary,
        effects=rewritten_effects,
        synthetic_expr=new_synthetic_expr,
    )


def _rewrite_parameter_expression_metadata(
    expr: Optional[Expression],
    params_by_index: Dict[int, Dict[str, Any]],
    params_by_storage: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[Expression]:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PARAMETER:
        descriptor = None
        has_index = isinstance(expr.value, int) and expr.value >= 0
        if has_index:
            descriptor = params_by_index.get(expr.value)
        else:
            storage_key = _storage_identity_key(getattr(expr, "storage_info", None))
            if storage_key is not None:
                descriptor = params_by_storage.get(storage_key)
        if descriptor is None:
            return expr

        desired_size = int(descriptor.get("size", 0) or 0)
        desired_type = descriptor.get("data_type") or expr.data_type
        desired_index = descriptor.get("index", expr.value)
        if (
            desired_size <= 0 or
            (
                desired_size == expr.size and
                desired_type == expr.data_type and
                desired_index == expr.value
            )
        ):
            return expr

        return Expression(
            expr_type=expr.expr_type,
            value=desired_index,
            operator=expr.operator,
            operands=list(expr.operands or []),
            size=desired_size,
            name=expr.name,
            data_type=desired_type,
            storage_info=expr.storage_info,
            read_order_key=expr.read_order_key,
            runtime_ref=getattr(expr, "runtime_ref", None),
            opcode=getattr(expr, "opcode", None),
        )

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            new_cond = None
            if cond is not None:
                new_cond_expr = _rewrite_parameter_expression_metadata(
                    cond.expression,
                    params_by_index,
                    params_by_storage,
                )
                new_cond = Condition(new_cond_expr, cond.negated)
                changed = changed or (new_cond_expr is not cond.expression)
            new_value = _rewrite_parameter_expression_metadata(
                value,
                params_by_index,
                params_by_storage,
            )
            changed = changed or (new_value is not value)
            branches.append((new_cond, new_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        rebuilt.data_type = expr.data_type
        rebuilt.data_type_obj = getattr(expr, "data_type_obj", None)
        rebuilt.storage_info = expr.storage_info
        rebuilt.read_order_key = expr.read_order_key
        return rebuilt

    operands = getattr(expr, "operands", None) or []
    if not operands:
        return expr

    new_operands = [
        _rewrite_parameter_expression_metadata(
            operand,
            params_by_index,
            params_by_storage,
        )
        for operand in operands
    ]
    if all(new is old for new, old in zip(new_operands, operands)):
        return expr

    return Expression(
        expr_type=expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=new_operands,
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=expr.read_order_key,
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _build_hints_by_object_identity(
    analysis: FunctionReturnAnalysis,
    hints: Dict[int, ParameterSemanticHint],
) -> Dict[Tuple[object, ...], ParameterSemanticHint]:
    hints_by_identity: Dict[Tuple[object, ...], ParameterSemanticHint] = {}
    for param in analysis.parameters or []:
        try:
            index = int(param.get("index"))
        except (TypeError, ValueError):
            continue
        if index < 0:
            continue
        hint = hints.get(index)
        if hint is None:
            continue
        hints_by_identity[("parameter_index", index)] = hint
        storage_key = _storage_identity_key(param.get("storage_info", param.get("storage")))
        if storage_key is not None:
            hints_by_identity[("parameter_storage", storage_key)] = hint
    return hints_by_identity
