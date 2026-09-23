# -*- coding: utf-8 -*-
"""比較の中で作った証拠と、その比較の最終 relation の束縛（Issue #167）。

relation の lifetime は「1 つの raw pair の比較」で、analysis object の lifetime では
ない。raw analysis は branch・retry・再帰抽象化の比較をまたいで生き残り、recovery
証拠（``completed_recovery_proof_evidence``）はその上に積まれる。比較の中で作った
証拠は、その比較の relation が含意した入力仮定・書き換え（``RewriteAuthorization``）
の下でだけ成り立つので、別の relation の比較へ持ち込んではならない。

束縛するのは relation の値（digest）で、比較 1 回ごとの identity ではない。同じ raw
pair を同じ relation で比べる branch（pairwise・loop template・monolithic・replan）は
証拠を共有してよい（同じ入力仮定の下の事実で、何についての proof かは proof の
object target が区別する）。relation の値が違う比較（例: 再帰抽象化が summary の
parameter を足した抽象 pair）とは共有しない。

契約:

* 比較の範囲: ``comparison_relation_scope(relation)`` が、1 つの比較の間だけ
  現在の relation を与える。開くのは relation を決めた dispatch の境界
  （``checker/strategy_execution.run_strategy_branch``）と、branch の結果の gate を
  その結果を作った比較の relation で実行する境界（``proof/obligations/stage_runner``）
  だけ。strategy は入口で自分の relation とこの範囲の relation の一致を確かめる
  （互換の直接呼び出しは自分の relation の範囲を開いて実行し直す）。入れ子の比較は
  自分の relation を push し、抜けると戻る。
* producer: 比較の中で証拠 record を作ったら ``bind_evidence_to_comparison`` で
  現在の relation の digest を record に記録する（relation を明示的に受け取った
  producer は ``bind_evidence_to_relation``）。比較の外で作った record には
  「比較の外」を記録し、どの比較でも採用されない。
* 後で実行する仕事と、その結果: worklist に積む producer / replanner は
  ``run_in_current_comparison`` で登録時の比較の relation を持ち運び、runtime は
  obligation の同一性と proof outcome をその relation ごとに分ける（runtime が一括で
  行う）。別の relation の比較で出た outcome が、この比較の reason を解消しない。
* consumer: gate は ``comparison_evidence`` を通してだけ証拠を読む。digest を
  持つ record は、現在の relation の digest と値で一致したときだけ残る。
  digest を持たない record は比較の前に関数単体で作った事実（analysis 層の
  recurrence 等）で、relation に依存しない。
* pair ledger: ``PairLedgerBinding.input_correspondence_digest`` がその ledger の
  closure の前提になった relation で、validator は現在の relation と照合する。

新しい証拠の producer は record を作るところで bind を 1 回呼ぶだけでよく、
consumer 側に照合を足さない。新しい relation の出所（IEE 等）も relation の digest
が変わるだけなので、この照合は変わらない。
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
from typing import Any, Callable, Iterable, Iterator, List, Mapping, MutableMapping, Optional, Tuple

from scripts.function_tracer_pcode.proof.formula.input_correspondence.model import (
    InputCorrespondenceSet,
)


#: 証拠 record の中で、それを作った比較の relation の digest を持つ key。
RELATION_DIGEST_KEY = "input_correspondence_digest"

#: 比較の外で作った record の印（どの relation の digest とも一致しない）。
OUTSIDE_COMPARISON = "outside_comparison"


@dataclass(frozen=True)
class _ComparisonScope:
    """1 つの比較の relation（``None`` は relation を与えられない比較）。"""

    relation: Optional[InputCorrespondenceSet]
    digest: Optional[str]


_CURRENT_COMPARISON: ContextVar[Optional[_ComparisonScope]] = ContextVar(
    "current_input_correspondence_comparison", default=None
)


def relation_digest(relation: Any) -> str:
    if type(relation) is not InputCorrespondenceSet:
        raise TypeError("relation binding requires the final InputCorrespondenceSet")
    return relation.digest


@contextmanager
def comparison_relation_scope(relation: Optional[InputCorrespondenceSet]) -> Iterator[None]:
    """1 つの比較の間、``relation`` をその比較の relation にする。

    ``None`` は「比較の relation が確定できない」範囲で、digest を持つ証拠を
    どれも採用しない（外側の比較の relation も引き継がない）。
    """

    scope = _ComparisonScope(None, None) if relation is None else _ComparisonScope(
        relation, relation_digest(relation)
    )
    token = _CURRENT_COMPARISON.set(scope)
    try:
        yield
    finally:
        _CURRENT_COMPARISON.reset(token)


class ComparisonBoundCallable:
    """登録した比較の relation の下で実行する callable（``run_in_current_comparison``）。"""

    __slots__ = ("_callback", "_scope")

    def __init__(self, callback: Callable[..., Any], scope: Optional[_ComparisonScope]) -> None:
        self._callback = callback
        self._scope = scope

    @property
    def relation_digest(self) -> Optional[str]:
        """この仕事を登録した比較の relation の digest（relation の無い比較では None）。"""

        return None if self._scope is None else self._scope.digest

    def __call__(self, *args: Any, **kwargs: Any) -> Any:
        token = _CURRENT_COMPARISON.set(self._scope)
        try:
            return self._callback(*args, **kwargs)
        finally:
            _CURRENT_COMPARISON.reset(token)


def run_in_current_comparison(callback: Callable[..., Any]) -> ComparisonBoundCallable:
    """後で実行する ``callback`` を、登録した比較の relation の下で実行する形にする。

    worklist の producer や replanner は、それを作った比較が終わった後に別の比較の
    範囲から実行されることがある。実行時の範囲ではなく登録時の範囲で照合する。
    既に束縛済みなら、そのまま（最初に登録した比較の relation を保つ）。
    """

    if isinstance(callback, ComparisonBoundCallable):
        return callback
    return ComparisonBoundCallable(callback, _CURRENT_COMPARISON.get())


def current_relation() -> Optional[InputCorrespondenceSet]:
    """現在の比較の最終 relation（比較の外、relation の無い比較では None）。"""

    scope = _CURRENT_COMPARISON.get()
    return None if scope is None else scope.relation


def comparison_uses_relation(relation: InputCorrespondenceSet) -> bool:
    """現在の比較の relation が ``relation`` か（strategy の入口で照合する）。

    strategy は自分の query・書き換えに使う relation と、証拠を束縛・照合する比較の
    relation が同じときだけ実行してよい。dispatch frame の経路では dispatch 境界が
    frame の relation で範囲を開くので常に一致する。
    """

    return relation_digest_is_current(relation_digest(relation))


def current_relation_digest() -> Optional[str]:
    """現在の比較の relation の digest（比較の外、relation の無い比較では None）。"""

    scope = _CURRENT_COMPARISON.get()
    return None if scope is None else scope.digest


def relation_digest_is_current(digest: Any) -> bool:
    """``digest`` が現在の比較の relation の digest と値で一致するか。"""

    current = current_relation_digest()
    return current is not None and isinstance(digest, str) and digest == current


def bind_evidence_to_relation(
    record: MutableMapping[str, Any], relation: InputCorrespondenceSet
) -> MutableMapping[str, Any]:
    """``relation`` の下で作った証拠 ``record`` に relation の digest を記録する。"""

    record[RELATION_DIGEST_KEY] = relation_digest(relation)
    return record


def bind_evidence_to_comparison(record: MutableMapping[str, Any]) -> MutableMapping[str, Any]:
    """現在の比較の中で作った証拠 ``record`` に、その比較の relation を記録する。"""

    record[RELATION_DIGEST_KEY] = current_relation_digest() or OUTSIDE_COMPARISON
    return record


def evidence_relation_binding_holds(record: Any) -> bool:
    """証拠 ``record`` を現在の比較で採用してよいか（照合の唯一の実装）。"""

    if not isinstance(record, Mapping):
        return False
    if RELATION_DIGEST_KEY not in record:
        return True
    return relation_digest_is_current(record.get(RELATION_DIGEST_KEY))


def comparison_evidence(records: Iterable[Any]) -> Tuple[Mapping[str, Any], ...]:
    """``records`` のうち、現在の比較で採用してよい証拠。"""

    return tuple(record for record in records or () if evidence_relation_binding_holds(record))


def _frozen(value: Any) -> Any:
    if isinstance(value, (list, tuple)):
        return tuple(_frozen(item) for item in value)
    return value


def evidence_merge_identity(record: Mapping[str, Any]) -> Tuple[Any, Any]:
    """証拠を合流するときの同一性（同じ proof でも relation が違えば別の証拠）。"""

    return (_frozen(record.get("proof_obligation_id")), record.get(RELATION_DIGEST_KEY))


def merge_new_evidence(
    existing: Iterable[Any], incoming: Iterable[Any]
) -> Optional[List[dict]]:
    """``existing`` に ``incoming`` の新しい証拠を足した列（増えなければ None）。"""

    records = [dict(record) for record in existing or () if isinstance(record, Mapping)]
    seen = {
        evidence_merge_identity(record)
        for record in records
        if record.get("proof_obligation_id") is not None
    }
    changed = False
    for record in incoming or ():
        if not isinstance(record, Mapping):
            continue
        identity = evidence_merge_identity(record)
        if identity[0] is not None and identity in seen:
            continue
        records.append(dict(record))
        if identity[0] is not None:
            seen.add(identity)
        changed = True
    return records if changed else None
