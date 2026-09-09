# -*- coding: utf-8 -*-
"""Issue #47 (PR-B): external placeholder callee の束縛ゼロ解析を再利用する。

``gammln`` / ``gser`` のような対象では、同じ callee（``log`` / ``exp``）が呼び出し
ごとに違う ``bound_signature`` で解析され、1 pair の中で数十回 decompile される。
その callee がこの binary に本体を持たない external placeholder なら、束縛値は解析へ
入りようがないので、束縛ゼロ scope で 1 回解析すれば足りる。

**再利用してよい条件（すべて満たす場合だけ）**

- ``resolve_effect_callee`` が external と確定している（解決が曖昧な thunk chain・
  分類 API 不通は対象外）
- decompile が完了している
- HighFunction が存在する
- High P-code の本体が無い（後述）

「本体が無い」の判定は「op が 0 個」ではない。Ghidra はこの binary に本体を持たない
external 記号を **``RETURN`` 1 個だけ**の HighFunction として復元する（実測: arm64
clang-O1 / mips64 gcc-O2 の ``log`` / ``exp`` / ``__stack_chk_fail`` がいずれも
``RETURN const:0x1``）。そこで本体不在の条件は「``RETURN`` 以外の op が無く、その
``RETURN`` も定数入力しか読まない」とする。op が 0 個の場合も当然これを満たす。
値入力を持つ ``RETURN``・他の op・読み取れない op 列はすべて不適格（fail closed）。

**soundness**: 束縛値が解析へ入る経路は ``_make_tracer`` と効果要約の構築、すなわち
High P-code op の varnode 解決だけである。varnode を 1 つも読まない本体では、どの
束縛値も置換され得ないので、解析結果は束縛に依存しない。external / thunk / 名前 /
空 body を「同じ意味」「副作用なし」の証拠にしているわけではなく、**この binary から
得られる解析結果が束縛に依存しない**ことだけを使う。

**返す object**: 再利用時は束縛ゼロ entry をそのまま返さず、要求された
``analysis_scope_key`` を持つ複製（view）を返す。scope key は cache の目印であると
同時に ``_analysis_is_fully_argument_specialized()`` の入力でもあるため、束縛ゼロの
key のまま下流へ渡すと呼び出し側の展開経路が別分岐に入ってしまう。view を返せば
下流から見た解析結果は従来と同一で、省けるのは decompile と解析そのものだけになる。
"""

from __future__ import annotations

import json
from contextlib import contextmanager
from typing import Any, Dict, Optional, Set, Tuple

from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
    resolution_is_confirmed_external,
    resolve_effect_callee,
)
from scripts.function_tracer_pcode.analysis.returns.lifecycle import (
    analysis_cache_target_identity,
)
from scripts.function_tracer_pcode.analysis.runtime_state import (
    UNBOUND_REUSE_CACHE_KEY_UNAVAILABLE,
    UNBOUND_REUSE_CALLEE_IS_INTERNAL,
    UNBOUND_REUSE_DECOMPILE_INCOMPLETE,
    UNBOUND_REUSE_ELIGIBLE,
    UNBOUND_REUSE_EXTERNAL_RESOLUTION_AMBIGUOUS,
    UNBOUND_REUSE_HIGH_FUNCTION_MISSING,
    UNBOUND_REUSE_PCODE_BODY_PRESENT,
    UNBOUND_REUSE_PCODE_BODY_UNREADABLE,
    UNBOUND_REUSE_UNBOUND_ANALYSIS_UNAVAILABLE,
    CalleeUnboundReuseVerdict,
)


#: eligibility 判定のための decompile に使う timeout（``_decompile_function`` 既定と同じ）。
CALLEE_UNBOUND_REUSE_PROBE_TIMEOUT = 60


def unbound_reuse_enabled() -> bool:
    from scripts.function_tracer_pcode.config import settings

    return bool(getattr(settings, "CALLEE_UNBOUND_REUSE_ENABLED", True))


def unbound_reuse_shadow_enabled() -> bool:
    from scripts.function_tracer_pcode.config import settings

    return bool(getattr(settings, "CALLEE_UNBOUND_REUSE_SHADOW", False))


def _exact_bool(value: Any) -> Optional[bool]:
    """Ghidra 側 API の返り値を厳密な bool としてだけ受け取る（不明は ``None``）。"""
    return value if type(value) is bool else None


def placeholder_body_ineligibility_reason(high_function: Any) -> Optional[str]:
    """「この binary に本体が無い」と言えない理由を返す（言えるなら ``None``）。

    ``RETURN`` 以外の op、値入力を持つ ``RETURN``、読み取れない op 列はすべて不適格。
    op が 1 つも無い HighFunction も本体不在として扱う。
    """

    if high_function is None:
        return UNBOUND_REUSE_HIGH_FUNCTION_MISSING
    try:
        blocks = high_function.getBasicBlocks()
    except Exception:
        return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
    if blocks is None:
        return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
    try:
        for block in blocks:
            iterator = block.getIterator()
            while iterator.hasNext():
                reason = _placeholder_op_ineligibility_reason(iterator.next())
                if reason is not None:
                    return reason
    except Exception:
        return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
    return None


def _placeholder_op_ineligibility_reason(op: Any) -> Optional[str]:
    if op is None:
        return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
    try:
        mnemonic = str(op.getMnemonic())
        input_count = int(op.getNumInputs())
        inputs = [op.getInput(index) for index in range(input_count)]
    except Exception:
        return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
    if mnemonic != "RETURN":
        return UNBOUND_REUSE_PCODE_BODY_PRESENT
    for varnode in inputs:
        if varnode is None:
            return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
        try:
            is_constant = _exact_bool(varnode.isConstant())
        except Exception:
            return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
        if is_constant is None:
            return UNBOUND_REUSE_PCODE_BODY_UNREADABLE
        if not is_constant:
            # 値を返す RETURN は、その値が束縛によって変わり得る。
            return UNBOUND_REUSE_PCODE_BODY_PRESENT
    return None


def shadow_projection(analysis: Any) -> str:
    """比較用の完全な構造投影。

    再利用側は要求された scope key を持つ view なので、cache scope 由来の metadata に
    も必然的な差は残らない。したがって正規化して隠す項目は無く、``binary_id`` を含む
    ``to_dict()`` 全体をそのまま比較する。
    """

    return json.dumps(analysis.to_dict(), sort_keys=True, default=repr)


def _observation_subject_key(analysis: Any) -> Tuple[Any, ...]:
    function_ref = getattr(analysis, "function_ref", None)
    stable_key = getattr(function_ref, "stable_key", None)
    return (
        getattr(analysis, "binary_id", None),
        getattr(analysis, "function_name", None),
        getattr(analysis, "entry_point", None),
        stable_key() if callable(stable_key) else None,
    )


def shadow_results_match(reused: Any, bound_sensitive: Any) -> bool:
    """shadow validation: 同じ観測対象どうしを完全投影で比較する。

    一致しないことは「再利用が間違い」の証明でも、一致することが正しさの証明でも
    ない。あくまで regression validation で、一致しなければ従来結果を採る。
    """

    if reused is None or bound_sensitive is None:
        return False
    if _observation_subject_key(reused) != _observation_subject_key(bound_sensitive):
        # 同じ program / binary / callee の観測でなければ比較対象にしない。
        return False
    return shadow_projection(reused) == shadow_projection(bound_sensitive)


def rebound_scope_view(analysis: Any, analysis_scope_key: Tuple[Any, ...]) -> Any:
    """束縛ゼロ解析を、要求された scope の view として複製する。

    ``semantic_successor()`` の copy policy を使うので、cache に残る束縛ゼロ entry と
    可変状態を共有しない。``analysis_scope_key`` は派生 authority の無効化表に無い
    （他の semantic 入力を変えない）ため、複製は scope key 以外そのまま残る。
    """

    return analysis.semantic_successor(analysis_scope_key=analysis_scope_key)


def _impl__callee_unbound_reuse_verdict(self, callee, identity: str) -> CalleeUnboundReuseVerdict:
    """callee ごとに 1 回だけ確定する静的判定（program が変われば取り直す）。"""

    program_identity = self._program_identity()
    cache_key = self._function_cache_key(callee)
    if cache_key is None:
        return CalleeUnboundReuseVerdict(
            eligible=False,
            reason=UNBOUND_REUSE_CACHE_KEY_UNAVAILABLE,
            program_identity=program_identity,
        )
    verdicts = self._callee_unbound_reuse_verdicts
    cached = verdicts.get(cache_key)
    if cached is not None and cached.program_identity == program_identity:
        return cached
    verdict = _classify_callee_for_unbound_reuse(self, callee, program_identity)
    verdicts[cache_key] = verdict
    self._callee_unbound_reuse_stats.record_verdict(identity, verdict)
    return verdict


def _classify_callee_for_unbound_reuse(self, callee, program_identity) -> CalleeUnboundReuseVerdict:
    try:
        resolution = resolve_effect_callee(callee, self._external_call_effect_policy)
    except Exception:
        return CalleeUnboundReuseVerdict(
            eligible=False,
            reason=UNBOUND_REUSE_EXTERNAL_RESOLUTION_AMBIGUOUS,
            program_identity=program_identity,
        )
    if getattr(resolution, "kind", None) == "analyze":
        # 本体を持つ internal callee。束縛ごとの解析は PR-47-B の対象外。
        return CalleeUnboundReuseVerdict(
            eligible=False,
            reason=UNBOUND_REUSE_CALLEE_IS_INTERNAL,
            program_identity=program_identity,
        )
    if not resolution_is_confirmed_external(resolution):
        # thunk chain が循環・長すぎ・target 不明、分類 API 不通など。external と確定
        # していないので従来経路のまま。
        return CalleeUnboundReuseVerdict(
            eligible=False,
            reason=UNBOUND_REUSE_EXTERNAL_RESOLUTION_AMBIGUOUS,
            program_identity=program_identity,
            resolution_reason=getattr(resolution, "reason", None),
        )

    results = self._decompile_function(callee, timeout=CALLEE_UNBOUND_REUSE_PROBE_TIMEOUT)
    if results is None:
        return CalleeUnboundReuseVerdict(
            eligible=False,
            reason=UNBOUND_REUSE_DECOMPILE_INCOMPLETE,
            program_identity=program_identity,
            resolution_reason=getattr(resolution, "reason", None),
        )
    try:
        high_function = results.getHighFunction()
    except Exception:
        high_function = None
    reason = placeholder_body_ineligibility_reason(high_function)
    if reason is not None:
        return CalleeUnboundReuseVerdict(
            eligible=False,
            reason=reason,
            program_identity=program_identity,
            resolution_reason=getattr(resolution, "reason", None),
        )
    return CalleeUnboundReuseVerdict(
        eligible=True,
        reason=UNBOUND_REUSE_ELIGIBLE,
        program_identity=program_identity,
        resolution_reason=getattr(resolution, "reason", None),
    )


@contextmanager
def _impl__suspended_callee_unbound_reuse(self):
    """再利用を一時的に止める（shadow validation の再入用）。"""
    previous = getattr(self, "_callee_unbound_reuse_suspended", False)
    self._callee_unbound_reuse_suspended = True
    try:
        yield
    finally:
        self._callee_unbound_reuse_suspended = previous


def _impl__reuse_unbound_placeholder_analysis(
    self,
    function,
    target_ref,
    analysis_scope_key: Tuple[Any, ...],
    bound_parameter_values: Optional[Dict[int, Any]],
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Any]],
    timeout: int,
    active_functions: Optional[Set[Tuple[Any, ...]]],
):
    """束縛付き要求を、束縛ゼロ解析の view で満たせるなら満たす（不可なら ``None``）。

    ``None`` を返した場合は呼び出し側が従来どおり解析する。判定・shadow・診断の
    どこで失敗しても ``None`` を返して従来経路へ戻すだけで、解析は止めない。
    """

    if not unbound_reuse_enabled():
        return None
    if not bound_parameter_values and not bound_parameter_storage_values:
        # 束縛ゼロ要求そのもの。ここが束縛ゼロ entry を作る唯一の経路。
        return None
    if getattr(self, "_callee_unbound_reuse_suspended", False):
        return None

    identity = analysis_cache_target_identity(target_ref)
    stats = self._callee_unbound_reuse_stats
    try:
        verdict = self._callee_unbound_reuse_verdict(function, identity)
        if not verdict.eligible:
            return None

        unbound_key = self._analysis_scope_key(function)
        unbound_analysis = self._call_analysis_cache.get(unbound_key)
        if unbound_analysis is None:
            unbound_analysis = self.analyze_function(
                function,
                timeout=timeout,
                active_functions=active_functions,
            )
            stats.record_unbound_analysis(identity)
        if unbound_analysis is None:
            stats.record_decline(identity, UNBOUND_REUSE_UNBOUND_ANALYSIS_UNAVAILABLE)
            return None

        reused = rebound_scope_view(unbound_analysis, analysis_scope_key)
        if unbound_reuse_shadow_enabled():
            return _shadow_validated_reuse(
                self,
                reused=reused,
                function=function,
                identity=identity,
                timeout=timeout,
                active_functions=active_functions,
                bound_parameter_values=bound_parameter_values,
                bound_parameter_storage_values=bound_parameter_storage_values,
            )
        # 従来経路と同じ key へ同じように残す（cache の構造も方針も変えない）。
        self._call_analysis_cache[analysis_scope_key] = reused
        stats.record_reuse(identity)
        return reused
    except Exception as exc:  # 再利用の失敗で解析を止めない
        self._debug_print(f"Unbound callee reuse skipped for '{identity}': {exc}")
        return None


def _shadow_validated_reuse(
    self,
    *,
    reused,
    function,
    identity: str,
    timeout: int,
    active_functions,
    bound_parameter_values,
    bound_parameter_storage_values,
):
    """再利用結果と従来の bound-sensitive 解析を両方作って比較する（regression validation）。

    一致しない場合は従来結果を採用する。shadow が有効な間は解析を省かないので、
    削減効果は測れない（正しさの回帰検査専用）。
    """

    stats = self._callee_unbound_reuse_stats
    try:
        with self._suspended_callee_unbound_reuse():
            bound_sensitive = self.analyze_function(
                function,
                timeout=timeout,
                active_functions=active_functions,
                bound_parameter_values=bound_parameter_values,
                bound_parameter_storage_values=bound_parameter_storage_values,
            )
        matched = shadow_results_match(reused, bound_sensitive)
    except Exception as exc:
        stats.record_shadow(identity, False)
        self._debug_print(f"Unbound callee reuse shadow failed for '{identity}': {exc}")
        return None
    stats.record_shadow(identity, matched)
    if matched:
        # 従来解析はすでに要求 scope の key へ入っている（内容は一致）。上書きしない。
        return reused
    self._debug_print(
        f"Unbound callee reuse shadow mismatch for '{identity}': keeping the bound-sensitive analysis"
    )
    return bound_sensitive
