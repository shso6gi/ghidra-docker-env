# -*- coding: utf-8 -*-
"""解析失敗の型と、握り潰した例外の記録先（Issue #125 PR-125-A）。

`checker` の catch-all は今まで「解析の限界」と「内部エラー」を区別できず、
どちらも `legacy_compatibility_error` の ERROR になっていた。ここでは

* `AnalysisLimitation`: 解析が **できなかった**（限界）。判定 authority の
  active cause へ帰属させる義務がある。帰属できなければ ERROR（fail-closed）。
* `InternalError`: 解析が **壊れた**（バグ・想定外の状態）。ERROR のまま、
  ただし `internal_exception` として分類し stack を診断に残す。
* `CauseAttributionKey`: 既存 cause へ帰属させたいときに、どの occurrence の
  ことかを **一意に** 指すためのキー。`authority` 側が `CauseIdV2` の再計算で
  照合する（`authority/decision/limitation_attribution.py`）。

を型で分ける。`log_swallowed` は「捕まえたが握り潰した例外」の件数だけを
process 単位で集めるための診断 sink で、**判定にも proof にも読ませない**
（`tests/unit/test_issue125_typed_failures.py` が source で固定する）。

Issue #106 PR-106-0 はここに **pair 単位の実行制御**（`PairExecutionControl` =
`PairFailureLedger` + `PairStopState`）を足す。低レベルの処理は
`raise_limitation()` / `record_internal_bug()` で「限界が起きた」ことを台帳へ
通知するだけで、**UNKNOWN / ERROR の最終判断・receipt・JSON・表示は一切持たない**
（それらは既存の authority / output 層が所有する）。台帳が例外とは別に事実を
持つので、途中の `except Exception` が限界を握り潰しても pair 境界で失われない。

dependency rule: この module は標準ライブラリ以外を import しない。`core` は
最下層なので、上位層（`authority` / `proof` / `checker` …）の型をここへ持ち
込むと層が壊れる。`CauseAttributionKey` が `IdentityScope` ではなくその
**値の文字列**を持つのはこのため（Enum の解決は authority 側の責務）。
"""

from __future__ import annotations

import hashlib
import threading
import traceback
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Iterator, List, NoReturn, Optional, Tuple


#: 既存 cause へ帰属させるときに指定できる identity scope の値（Enum は authority 側）。
IDENTITY_SCOPE_VALUES = frozenset({"UNARY", "RELATIONAL"})

#: `InternalError` の診断に残す stack の最大行数。
STACK_LINE_LIMIT = 64


def _exact_tuple(value: Any) -> tuple:
    """tuple / list は tuple 化し、単独値は 1 要素 tuple にする（str は単独値）。"""
    if isinstance(value, tuple):
        return value
    if isinstance(value, list):
        return tuple(value)
    if value is None:
        return ()
    return (value,)


@dataclass(frozen=True)
class CauseAttributionKey:
    """既存 active cause 1 件を一意に指すためのキー。

    `authority` 側は、このキーから `CauseIdV2` を **再計算** して
    `c_active_base` の `cause_id` と突き合わせる。再計算に必要な入力は
    `CauseIdV2.create()` の引数そのもの（`semantic_proposition` だけでは
    `semantic_proposition_digest` を再現できない）なので、proposition を構成する
    3 つの補助入力もここに持つ。`target_kind` は digest に含まれないため
    authority 側が独立に照合する。

    `proof_requirement_ids` は **完全一致** で照合される。部分集合・上位集合は
    帰属とみなさない。空 tuple は「帰属先も requirement を持たない」ことを
    主張する値で、照合の省略ではない。
    """

    reason_id: str
    identity_scope: str
    target_kind: str
    canonical_target_key: tuple
    missing_semantic_fact: tuple
    semantic_proposition: tuple
    proof_requirement_ids: Tuple[str, ...]
    observation_surface: Any = ()
    active_semantic_precondition: Any = ()
    correspondence_contract: Any = None

    def __post_init__(self) -> None:
        for name in (
            "canonical_target_key", "missing_semantic_fact", "semantic_proposition",
        ):
            object.__setattr__(self, name, _exact_tuple(getattr(self, name)))
        object.__setattr__(
            self, "proof_requirement_ids", tuple(self.proof_requirement_ids)
        )
        if type(self.reason_id) is not str or not self.reason_id:
            raise ValueError("cause attribution key needs an exact reason id")
        if self.identity_scope not in IDENTITY_SCOPE_VALUES:
            raise ValueError("cause attribution key needs a known identity scope value")
        if type(self.target_kind) is not str or not self.target_kind:
            raise ValueError("cause attribution key needs an exact target kind")
        if any(
            type(item) is not str or not item
            for item in self.proof_requirement_ids
        ):
            raise TypeError("proof requirement ids must be non-empty exact strings")
        if len(self.proof_requirement_ids) != len(set(self.proof_requirement_ids)):
            raise ValueError("duplicate proof requirement id in cause attribution key")


class AnalysisFailureError(Exception):
    """解析が完了しなかったことを表す型の基底。"""


class AnalysisLimitation(AnalysisFailureError):
    """解析の限界（できなかった）。判定 authority の cause に帰属する義務がある。

    `attribution` を与えた場合だけ既存 cause への帰属を試みる。与えない場合は
    「その限界を表す reason を所有する producer」経由で新しい cause を作る。
    どちらもできなければ ERROR（`limitation_unattributed`）に落ちる。
    """

    def __init__(
        self,
        reason_id: str,
        detail: str,
        *,
        site: str,
        target_key: Any = (),
        missing_semantic_fact: Any = (),
        evidence_refs: Any = (),
        attribution: Optional[CauseAttributionKey] = None,
    ) -> None:
        if type(reason_id) is not str or not reason_id:
            raise ValueError("analysis limitation needs an exact reason id")
        if type(site) is not str or not site:
            raise ValueError("analysis limitation needs an exact observation site")
        if attribution is not None and type(attribution) is not CauseAttributionKey:
            raise TypeError("analysis limitation attribution must be an exact key")
        super().__init__(f"{reason_id}: {detail}")
        self.reason_id = reason_id
        self.detail = str(detail)
        self.site = site
        self.target_key = _exact_tuple(target_key)
        self.missing_semantic_fact = (
            _exact_tuple(missing_semantic_fact)
            or ("analysis_limitation_unresolved", reason_id)
        )
        self.evidence_refs = tuple(
            str(item) for item in _exact_tuple(evidence_refs)
        )
        self.attribution = attribution


class InternalError(AnalysisFailureError):
    """内部エラー（壊れた）。`__cause__` に元の例外を保持する。"""

    def __init__(self, cause: BaseException, *, site: str) -> None:
        if not isinstance(cause, BaseException):
            raise TypeError("internal error requires the original exception")
        if type(site) is not str or not site:
            raise ValueError("internal error needs an exact observation site")
        super().__init__(f"{type(cause).__name__}: {cause}")
        self.site = site
        self.exception_type = type(cause).__name__
        self.__cause__ = cause

    def stack_lines(self, limit: int = STACK_LINE_LIMIT) -> Tuple[str, ...]:
        """元の例外の stack を最大 ``limit`` 行で返す（診断は失敗しない）。"""
        cause = self.__cause__
        try:
            lines = traceback.format_exception(
                type(cause), cause, cause.__traceback__
            )
        except Exception:  # 診断は判定を壊さない
            return ()
        rows: List[str] = []
        for chunk in lines:
            rows.extend(chunk.rstrip("\n").splitlines())
        return tuple(rows[-limit:]) if limit > 0 else tuple(rows)

    def stack_digest(self, limit: int = STACK_LINE_LIMIT) -> str:
        """stack の内容に対する安定な digest（同じ stack なら同じ値）。"""
        payload = "\n".join(self.stack_lines(limit))
        return hashlib.sha256(payload.encode("utf-8", "replace")).hexdigest()


class FrozenExpressionError(AnalysisFailureError):
    """凍結済みの意味 object を書き換えようとした（内部バグ、Issue #22 / #106）。

    `TypeError` / `AttributeError` / `ValueError` の派生に **しない**。派生に
    すると `_CONDITION_RECOVERABLE_ERRORS` のような「回復可能」tuple に吸収され、
    バグが UNKNOWN や `None` に化けてしまう。限界（`AnalysisLimitation`）でも
    ないので、帰属先 cause を探さずそのまま ERROR へ落とす。
    """


class ExpressionCycleError(AnalysisFailureError):
    """意味 graph に閉路を見つけた（内部バグ、Issue #22 / #106）。

    `FrozenExpressionError` と同じ理由で標準の型階層へは混ぜない。
    """


class DeadlineExceeded(AnalysisLimitation):
    """解析の予算（時間・段数）を使い切って打ち切った限界。

    実際に raise する経路の導入は #106 の責務。ここでは型と reason id だけを
    先に固定し、catch 側と帰属契約を先に作る。
    """

    REASON_ID = "analysis_budget_exceeded"

    def __init__(
        self,
        detail: str,
        *,
        site: str,
        target_key: Any = (),
        missing_semantic_fact: Any = (),
        evidence_refs: Any = (),
        attribution: Optional[CauseAttributionKey] = None,
    ) -> None:
        super().__init__(
            self.REASON_ID,
            detail,
            site=site,
            target_key=target_key,
            missing_semantic_fact=missing_semantic_fact,
            evidence_refs=evidence_refs,
            attribution=attribution,
        )


# ---------------------------------------------------------------------------
# pair 単位の実行制御（Issue #106 PR-106-0）
# ---------------------------------------------------------------------------
#
# 所有するもの: 限界 event、内部バグ、stop state、pair / session の lifecycle。
# 所有しないもの: UNKNOWN / ERROR の最終判断、receipt、JSON、表示。
#
# 例外だけで伝えると、途中の `except Exception` に握り潰された瞬間に「限界が
# あった」事実そのものが消える。台帳は例外と **独立に** 事実を持つので、握り
# 潰されても pair 境界（`authority/lifecycle/production_boundary.py`）が拾える。


class PairStopState(Enum):
    """pair 1 件の実行をどこまで進めてよいか。

    `allows_finalization()` が全値で真なのは意図どおり。解析を止めることと、
    既に確定した判定を authority に確定させて receipt / JSON を出すことは別で、
    後者を止めると「限界で止めたのに結果が無い」状態になってしまう。
    """

    NONE = "NONE"
    PAIR_TERMINAL_LIMITATION = "PAIR_TERMINAL_LIMITATION"
    PAIR_TERMINAL_DEADLINE = "PAIR_TERMINAL_DEADLINE"
    INTERNAL_BUG = "INTERNAL_BUG"

    def allows_semantic_analysis(self) -> bool:
        """新しい意味解析（phase 再解析・conditional lane・新規 query）を始めてよいか。"""
        return self is PairStopState.NONE

    def allows_finalization(self) -> bool:
        """確定処理（authority finalize・receipt・serialization・teardown）を続けてよいか。"""
        return True


#: **軸 D: stop state → 実行の厳しさ**。`_append` の escalation だけが読む。
#: ここを変えても「どの failure を結果化するか」は変わらない（軸 B が別表）。
_STOP_STATE_RANK = {
    PairStopState.NONE: 0,
    PairStopState.PAIR_TERMINAL_LIMITATION: 1,
    PairStopState.PAIR_TERMINAL_DEADLINE: 1,
    PairStopState.INTERNAL_BUG: 2,
}


def _represented_exception_ids(exc: BaseException) -> set:
    """この例外 object が台帳の中で表している識別子の集合。

    `InternalError` は原因を包んだだけなので、包む前と包んだ後を同じ 1 件として
    扱えるように両方の id を返す。
    """
    ids = {id(exc)}
    if isinstance(exc, InternalError) and exc.__cause__ is not None:
        ids.add(id(exc.__cause__))
    return ids


class PairFailureKind(Enum):
    """pair を止めた failure の種別。**結果の種類** と 1 対 1 に対応する。

    失敗の *クラス* が増えても（`FrozenExpressionError` / `ExpressionCycleError` /
    新しい `AnalysisLimitation` 派生）この enum は増えない。増えるとしたら
    「UNKNOWN でも `internal_exception` ERROR でもない、新しい結果の種類」を
    足すときだけで、そのときは consumer 側の変換表 1 箇所が対応点になる。
    """

    LIMITATION = "limitation"
    INTERNAL_BUG = "internal_bug"


#: **軸 B: failure kind → 結果化の優先順位**（大きいほど勝つ）。
#: 「どの failure を結果にするか」だけを決める。stop state の強さ（軸 D）とは
#: 独立で、片方を変えても他方は変わらない。
_FAILURE_KIND_RANK = {
    PairFailureKind.LIMITATION: 0,
    PairFailureKind.INTERNAL_BUG: 1,
}

#: **軸 C: failure kind → 取り得る stop state**。既定は先頭要素。
#: `record_limitation(stop=...)` の検証もここを読む（種別に意味の無い stop state
#: を受け付けない）。種別を足したらここへ 1 行足す。
_STOP_STATES_BY_KIND = {
    PairFailureKind.LIMITATION: (
        PairStopState.PAIR_TERMINAL_LIMITATION,
        PairStopState.PAIR_TERMINAL_DEADLINE,
    ),
    PairFailureKind.INTERNAL_BUG: (PairStopState.INTERNAL_BUG,),
}


@dataclass(frozen=True)
class PairPendingFailure:
    """今この pair を止めている failure 1 件。**consumer が読む唯一の形**。

    優先順位（内部バグ > 限界）は台帳が解決済みなので、consumer は「どちらが
    勝つか」を知らなくてよい。`exception` は結果化にそのまま渡せる canonical 型
    （`INTERNAL_BUG` なら `InternalError`、`LIMITATION` なら `AnalysisLimitation`）
    で、記録された生の例外型は外へ出さない。
    """

    kind: PairFailureKind
    stop_state: PairStopState
    site: str
    exception: BaseException

    @property
    def is_internal_bug(self) -> bool:
        return self.kind is PairFailureKind.INTERNAL_BUG


@dataclass(frozen=True)
class _PairFailureRecord:
    """台帳の内部表現（この module の外へは出さない）。"""

    kind: PairFailureKind
    site: str
    reason_id: Optional[str]
    target_key: tuple
    exception: BaseException
    stop_state: PairStopState

    @property
    def fold_key(self) -> Tuple[str, str, Optional[str], tuple]:
        """同じ failure の再記録を 1 件に畳むためのキー。"""
        return (self.kind.value, self.site, self.reason_id, self.target_key)

    def canonical_exception(self) -> BaseException:
        """結果化に使える型へ正規化した例外。

        内部バグは `InternalError` に包む（既に包んであるならそのまま）。観測点は
        **記録した場所** で、拾い直した gate の場所ではない。
        """
        if self.kind is not PairFailureKind.INTERNAL_BUG:
            return self.exception
        if isinstance(self.exception, InternalError):
            return self.exception
        return InternalError(self.exception, site=self.site)

    def as_pending(self) -> PairPendingFailure:
        return PairPendingFailure(
            kind=self.kind,
            stop_state=self.stop_state,
            site=self.site,
            exception=self.canonical_exception(),
        )


def _default_stop_state(kind: PairFailureKind, exc: BaseException) -> PairStopState:
    """**軸 C の owner**: 種別（と例外型）から既定の stop state を決める。

    時間予算だけが deadline で、派生型も deadline として扱う。それ以外は種別の
    既定（`_STOP_STATES_BY_KIND` の先頭）。
    """
    if kind is PairFailureKind.LIMITATION and isinstance(exc, DeadlineExceeded):
        return PairStopState.PAIR_TERMINAL_DEADLINE
    return _STOP_STATES_BY_KIND[kind][0]


def _checked_stop_state(
    kind: PairFailureKind, stop_state: PairStopState,
) -> PairStopState:
    """種別に対して意味のある stop state かを検証する（軸 C の一部）。

    限界に `INTERNAL_BUG` を、内部バグに `PAIR_TERMINAL_LIMITATION` を渡すような
    組み合わせは、順位の解釈を壊すのでその場で拒否する（黙って通さない）。
    """
    allowed = _STOP_STATES_BY_KIND[kind]
    if stop_state not in allowed:
        raise ValueError(
            f"stop state {stop_state.value} is not meaningful for "
            f"{kind.value}; allowed: {[state.value for state in allowed]}"
        )
    return stop_state


def _limitation_record(
    exc: "AnalysisLimitation", stop_state: PairStopState,
) -> _PairFailureRecord:
    return _PairFailureRecord(
        kind=PairFailureKind.LIMITATION,
        site=exc.site,
        reason_id=exc.reason_id,
        target_key=exc.target_key,
        exception=exc,
        stop_state=stop_state,
    )


def _internal_bug_record(exc: BaseException, site: str) -> _PairFailureRecord:
    return _PairFailureRecord(
        kind=PairFailureKind.INTERNAL_BUG,
        site=site,
        reason_id=None,
        target_key=(type(exc).__name__,),
        exception=exc,
        stop_state=_default_stop_state(PairFailureKind.INTERNAL_BUG, exc),
    )


def classify_failure_kind(exc: BaseException) -> Optional[PairFailureKind]:
    """**軸 A の owner**: 例外型 → failure kind（族の外なら `None`）。

    `AnalysisFailureError` 族のうち `AnalysisLimitation` は限界、それ以外
    （`InternalError` / `FrozenExpressionError` / `ExpressionCycleError` …）は
    内部バグ。gate の catch 族（`AnalysisFailureError`）と producer の受理範囲は
    この 1 関数で一致する。新しい failure class は族を継承するだけでここに乗る。
    """
    if isinstance(exc, AnalysisLimitation):
        return PairFailureKind.LIMITATION
    if isinstance(exc, AnalysisFailureError):
        return PairFailureKind.INTERNAL_BUG
    return None


def classify_internal_bug_kind(exc: BaseException) -> Optional[PairFailureKind]:
    """`record_internal_bug` が受理するかの判定（軸 A の再利用）。"""
    return classify_failure_kind(exc)


def classify_typed_failure(exc: BaseException) -> Optional[_PairFailureRecord]:
    """typed failure 1 件を台帳の記録へ落とす。**例外型 → 種別の対応はここだけ**。

    種別の判定は `classify_failure_kind`（軸 A）に委ね、ここは「種別 → 記録の
    組み立て」だけを行う。族の外の例外は `None`（従来の generic 経路）。
    """
    kind = classify_failure_kind(exc)
    if kind is PairFailureKind.LIMITATION:
        return _limitation_record(exc, _default_stop_state(kind, exc))
    if kind is PairFailureKind.INTERNAL_BUG:
        site = (
            exc.site if isinstance(exc, InternalError)
            else _site_of_unrecorded(exc)
        )
        return _internal_bug_record(exc, site)
    return None


class PairExecutionControl:
    """pair 境界が持つ実行制御の **安定 interface**（`PairFailureLedger` が実装）。

    consumer（workflow / reanalysis / checker / production boundary）はこの 6 つ
    しか使わない。記録の保存形式・畳み込み・優先順位の解決・stop state の
    escalation は **すべて実装側** にあるので、それらを変えても consumer は
    変わらない。診断・test 専用の窓口はここに入れない（実装側に置く）。
    """

    def record_limitation(
        self, exc: "AnalysisLimitation", *, stop: Optional[PairStopState] = None,
    ) -> None:
        raise NotImplementedError

    def record_internal_bug(self, exc: BaseException, *, site: str) -> None:
        raise NotImplementedError

    def pending_failure(self) -> Optional[PairPendingFailure]:
        """優先順位を解決した「今この pair を止めている failure」（無ければ `None`）。"""
        raise NotImplementedError

    def stop_state(self) -> PairStopState:
        raise NotImplementedError

    def allows_semantic_analysis(self) -> bool:
        raise NotImplementedError

    def allows_finalization(self) -> bool:
        raise NotImplementedError


class PairFailureLedger(PairExecutionControl):
    """1 pair / 1 session ぶんの failure 記録・畳み込み・優先順位・stop state。

    `pair_identity` と `session_identity` の **両方** が一致する再入だけが同じ
    台帳を共有する（同 pair の phase 再解析・再帰 `check()`・recurrence
    promotion）。別 pair / 別 session は別の台帳になり、外側へ漏れない。
    """

    def __init__(self, pair_identity: Any, session_identity: Any) -> None:
        self.pair_identity = pair_identity
        self.session_identity = session_identity
        self._records: List[_PairFailureRecord] = []
        self._fold_keys: set = set()
        self._exception_ids: set = set()
        self._stop_state = PairStopState.NONE

    # -- identity ----------------------------------------------------------

    def matches(self, pair_identity: Any, session_identity: Any) -> bool:
        return (
            self.pair_identity == pair_identity
            and self.session_identity == session_identity
        )

    # -- 記録 --------------------------------------------------------------

    def record_limitation(
        self, exc: "AnalysisLimitation", *, stop: Optional[PairStopState] = None,
    ) -> None:
        if not isinstance(exc, AnalysisLimitation):
            raise TypeError("pair ledger records exact analysis limitations")
        kind = PairFailureKind.LIMITATION
        stop_state = _checked_stop_state(
            kind, stop if stop is not None else _default_stop_state(kind, exc),
        )
        self._append(_limitation_record(exc, stop_state))

    def record_internal_bug(self, exc: BaseException, *, site: str) -> None:
        """内部バグを 1 件記録する。

        受け付けるのは **gate が受けられる型だけ**（`AnalysisFailureError` 族の
        うち限界でないもの）。記録だけ成功して、raise された生の例外が境界を
        素通りする状態を作らないための制限で、族の外の例外はここで拒否する
        （`InternalError` に包んでから渡す）。
        """
        if type(site) is not str or not site:
            raise ValueError("an internal bug record needs an exact observation site")
        if classify_internal_bug_kind(exc) is not PairFailureKind.INTERNAL_BUG:
            raise TypeError(
                "pair ledger records internal bugs the boundary can also catch: "
                f"{type(exc).__name__} is not an AnalysisFailureError that is not "
                "an AnalysisLimitation; wrap it in InternalError first"
            )
        self._append(_internal_bug_record(exc, site))

    def _append(self, record: _PairFailureRecord) -> None:
        if not self._already_recorded(record):
            self._fold_keys.add(record.fold_key)
            self._exception_ids.update(_represented_exception_ids(record.exception))
            self._records.append(record)
        if _STOP_STATE_RANK[record.stop_state] > _STOP_STATE_RANK[self._stop_state]:
            self._stop_state = record.stop_state

    def _already_recorded(self, record: _PairFailureRecord) -> bool:
        """同じ failure の再記録か。畳む条件は 2 つ。

        (a) `(種別, 観測点, reason, target)` が同じ再 raise。
        (b) **同じ例外 object**。`raise` したものを上位の gate が拾い直す経路が
            あるので、観測点が違っても 2 件に増やさない（`InternalError` に
            包み直されている場合は、包まれた原因で一致させる）。
        """
        if record.fold_key in self._fold_keys:
            return True
        return bool(
            _represented_exception_ids(record.exception) & self._exception_ids
        )

    # -- 参照 --------------------------------------------------------------

    def stop_state(self) -> PairStopState:
        return self._stop_state

    def allows_semantic_analysis(self) -> bool:
        return self._stop_state.allows_semantic_analysis()

    def allows_finalization(self) -> bool:
        return self._stop_state.allows_finalization()

    def pending_failure(self) -> Optional[PairPendingFailure]:
        """優先順位を解決した failure 1 件。

        順位は **failure kind**（`_FAILURE_KIND_RANK`、軸 B）だけで決める。
        同じ種別なら記録順の先頭。stop state の強さ（軸 D）は実行をどこまで
        止めるかの話で、ここには効かない — stop state の値や順位を変えても
        「内部バグが限界に勝つ」は動かない。
        """
        if not self._records:
            return None
        winner = max(
            enumerate(self._records),
            key=lambda item: (_FAILURE_KIND_RANK[item[1].kind], -item[0]),
        )[1]
        return winner.as_pending()

    # -- 診断・test 専用（安定 contract には含めない） ----------------------

    def recorded_failure_count(self) -> int:
        """畳み込み後の記録件数。

        production の consumer は呼ばない（`PairExecutionControl` に無い）。
        畳み込みが効いているかを test / 診断から確かめるためだけの窓口。
        """
        return len(self._records)


# 台帳の stack。**process = pair 1 件 + 同期的な入れ子実行** を前提に module
# 単位で持つ（thread local ではない）。
#
# thread に関する契約（Issue #106 PR-106-0）:
#   * scope の開閉と `raise_limitation` / `record_internal_bug` は、pair 境界と
#     同じ thread（= 同期的な入れ子の内側）から呼ぶことを前提にする。
#   * 別 thread から呼んでも例外にはならず「そのとき最内の scope」へ入る。pair が
#     1 つしか開いていない間は正しく届くが、**入れ子で別 pair の scope が開いて
#     いる最中** に外側 pair の worker thread が記録すると内側の台帳へ入る。
#   * したがって **arbitrary worker thread からの producer は一般の extension
#     point として保証しない**。solver worker のような非同期 producer から
#     failure を上げたくなったら、先にこの契約を決め直すこと（PR-106-A は
#     checkpoint を worker 内に置かない方針なので、現状この経路は存在しない）。
_PAIR_LEDGER_LOCK = threading.Lock()
_PAIR_LEDGERS: List[PairFailureLedger] = []


def current_pair_ledger() -> Optional[PairFailureLedger]:
    """今いちばん内側で開いている pair の台帳（無ければ `None`）。"""
    with _PAIR_LEDGER_LOCK:
        return _PAIR_LEDGERS[-1] if _PAIR_LEDGERS else None


@contextmanager
def pair_failure_scope(
    pair_identity: Any, session_identity: Any,
) -> Iterator[PairFailureLedger]:
    """pair 1 件の実行制御 scope。

    いちばん内側の台帳が `pair_identity` / `session_identity` の **両方** で
    一致するなら、その台帳をそのまま貸す（再入）。片方でも違えば新しい台帳を
    積み、scope を抜けるときに捨てる。捨てるので次 pair へ状態が漏れない。

    前提は **process = pair 1 件 + 同期的な入れ子実行**。別 thread からの
    producer は一般の extension point として保証しない（`_PAIR_LEDGERS` の
    コメントを参照）。
    """
    with _PAIR_LEDGER_LOCK:
        active = _PAIR_LEDGERS[-1] if _PAIR_LEDGERS else None
        reentrant = active is not None and active.matches(
            pair_identity, session_identity
        )
        if reentrant:
            ledger = active
        else:
            ledger = PairFailureLedger(pair_identity, session_identity)
            _PAIR_LEDGERS.append(ledger)
    try:
        yield ledger
    finally:
        if not reentrant:
            with _PAIR_LEDGER_LOCK:
                if _PAIR_LEDGERS and _PAIR_LEDGERS[-1] is ledger:
                    _PAIR_LEDGERS.pop()
                elif ledger in _PAIR_LEDGERS:
                    # 入れ子が正しく閉じなかった場合でも、この台帳から上は
                    # まとめて捨てる（次 pair へ持ち越さないことを優先する）。
                    del _PAIR_LEDGERS[_PAIR_LEDGERS.index(ledger):]


def pending_pair_failure() -> Optional[PairPendingFailure]:
    """今の pair を止めている failure（scope の外では `None`）。

    consumer 側の入口はこれ 1 つで、台帳の保存形式にも優先順位の規則にも触れない。
    """
    ledger = current_pair_ledger()
    return None if ledger is None else ledger.pending_failure()


def adopt_pair_failure(exc: BaseException) -> Optional[PairPendingFailure]:
    """境界を抜けようとしている例外を canonical failure へ解決する。

    1. 例外自体が typed failure なら、まだ台帳に無くてもここで記録する
       （`classify_typed_failure` が型 → 記録の対応を持つ）。`raise_limitation`
       を経由せずに raise された限界も、`record_internal_bug` してそのまま
       raise された内部バグも、**同じ 1 本の経路** に載せるため。
    2. そのうえで台帳の優先順位解決の結果を返す。記録済みの内部バグがあれば、
       今 raise されているのが限界でも内部バグが勝つ。
    3. typed failure でもなく台帳も空なら `None`（呼び出し側は従来の generic
       経路へ落とす）。
    """
    record = classify_typed_failure(exc)
    ledger = current_pair_ledger()
    if ledger is not None:
        if record is not None:
            ledger._append(record)
        return ledger.pending_failure()
    # scope の外（`check()` を直接呼ぶ test など）でも型だけは正規化する。
    return None if record is None else record.as_pending()


def _site_of_unrecorded(exc: BaseException) -> str:
    """記録されずに上がってきた typed failure の観測点（型名で代用する）。"""
    return f"core.errors.unrecorded:{type(exc).__name__}"


def raise_limitation(
    exc: AnalysisLimitation, *, stop: Optional[PairStopState] = None,
) -> NoReturn:
    """限界を台帳へ記録してから raise する（記録が先、例外は後）。

    先に記録するのは、途中の `except Exception` が例外を握り潰しても
    「限界があった」事実を pair 境界が読めるようにするため。
    """
    if not isinstance(exc, AnalysisLimitation):
        raise TypeError("raise_limitation needs an exact analysis limitation")
    ledger = current_pair_ledger()
    if ledger is not None:
        ledger.record_limitation(exc, stop=stop)
    raise exc


def record_internal_bug(exc: BaseException, *, site: str) -> None:
    """内部バグを台帳へ記録する（raise はしない。呼び出し側がそのまま raise する）。

    記録したあと生の例外をそのまま上へ投げてよい。握り潰されれば gate が台帳から
    拾い直し、握り潰されずに境界まで来れば `adopt_pair_failure` が拾う。どちらの
    経路でも `internal_exception` の ERROR に落ちる。
    """
    ledger = current_pair_ledger()
    if ledger is not None:
        ledger.record_internal_bug(exc, site=site)


def reset_pair_failure_scopes() -> None:
    """台帳 stack を空にする（ペア 1 件の実行の冒頭で呼ぶ二重の保証）。"""
    with _PAIR_LEDGER_LOCK:
        _PAIR_LEDGERS.clear()


# ---------------------------------------------------------------------------
# 握り潰した例外の台帳（診断専用）
# ---------------------------------------------------------------------------
#
# key = (site, exception_type, reason_id)。`site` は行番号を含まない安定文字列
# にする（行が動いても集計が割れないため）。値は件数だけで、例外オブジェクトも
# stack も保持しない（保持すると結果 JSON が膨らみ、参照も残る）。

_LEDGER_LOCK = threading.Lock()
_SWALLOWED: Dict[Tuple[str, str, Optional[str]], int] = {}


def log_swallowed(
    reason_id: Optional[str], exc: BaseException, site: str,
) -> None:
    """握り潰した例外を 1 件数える。診断なので、この関数自体は例外を出さない。"""
    try:
        key = (
            str(site),
            type(exc).__name__,
            None if reason_id is None else str(reason_id),
        )
    except Exception:
        return
    with _LEDGER_LOCK:
        _SWALLOWED[key] = _SWALLOWED.get(key, 0) + 1


def swallowed_exception_snapshot() -> List[Dict[str, Any]]:
    """現時点の集計を安定順の行にして返す（呼んでも集計は消えない）。

    `reason_id` は `None` を取り得るので、順序付けは文字列へ寄せてから行う
    （`None` と `str` を直接比べると TypeError になる）。
    """
    with _LEDGER_LOCK:
        rows = sorted(
            _SWALLOWED.items(),
            key=lambda item: (item[0][0], item[0][1], item[0][2] or ""),
        )
    return [
        {
            "site": site,
            "exception_type": exception_type,
            "reason_id": reason_id,
            "count": count,
        }
        for (site, exception_type, reason_id), count in rows
    ]


def swallowed_exception_total() -> int:
    """握り潰した例外の合計件数。"""
    with _LEDGER_LOCK:
        return sum(_SWALLOWED.values())


def reset_swallowed_exceptions() -> None:
    """集計を空にする（ペア 1 件の実行の冒頭で呼ぶ）。"""
    with _LEDGER_LOCK:
        _SWALLOWED.clear()
