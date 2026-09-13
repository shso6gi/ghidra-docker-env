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

dependency rule: この module は標準ライブラリ以外を import しない。`core` は
最下層なので、上位層（`authority` / `proof` / `checker` …）の型をここへ持ち
込むと層が壊れる。`CauseAttributionKey` が `IdentityScope` ではなくその
**値の文字列**を持つのはこのため（Enum の解決は authority 側の責務）。
"""

from __future__ import annotations

import hashlib
import threading
import traceback
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple


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
