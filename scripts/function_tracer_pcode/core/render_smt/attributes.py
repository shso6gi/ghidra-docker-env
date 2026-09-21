# -*- coding: utf-8 -*-
"""描画で使う **node 属性** の評価（反復 + DAG memo）。

幅・Bool sort・符号拡張の好み・「木のどこかに符号比較があるか」は、どれも
「子の答えから自分の答えを決める」形をしている。素朴に書くと再帰になり、

* 深い式で Python の再帰制限に当たる
* 共有部分式を親ごとに数え直すので DAG で指数になる
* 描画 1 回のあいだ同じ node の幅を何度も計算し直す

の 3 つが同時に起きる。ここが持つのは **走り方** だけで、node ごとの規則は
呼び出し側（`widths.py` / `render.py`）に残す。規則を変えたい人がこの module を
読む必要はなく、逆にここを変えても規則は動かない。

`render_attribute_scope()` の中では答えを描画 1 回分だけ覚える。属性は node の
純関数（描画文脈に依らない）なので、同じ描画のあいだ覚えても答えは変わらない。
scope の外では呼び出し 1 回分の memo になる（今までと同じ寿命）。
"""

from __future__ import annotations

import threading
from contextlib import contextmanager
from typing import Any, Callable, Dict, List, Tuple

from scripts.function_tracer_pcode.core.render_plan import (
    DISCOVERY_IGNORED_FAILURES,
    ResolutionSchedule,
)


class _NeedValue(BaseException):
    """子の答えがまだ無い、という内部の合図。

    `BaseException` 派生。属性計算の呼び出し元には `except Exception` の回復
    handler があり（`widths.py` / `loop_lowering.py`）、そこへ吸われると同じ node を
    回し続ける。
    """


_LOCAL = threading.local()


@contextmanager
def render_attribute_scope():
    """描画 1 回のあいだ属性の答えを共有する。

    入れ子の scope は外側の memo をそのまま使う（同じ描画の一部なので答えは
    同じ）。scope を抜けると memo は捨てる — 凍結していない式が後から変わる
    可能性を跨いで覚え続けない。
    """

    previous = getattr(_LOCAL, "caches", None)
    if previous is None:
        _LOCAL.caches = {}
    try:
        yield
    finally:
        _LOCAL.caches = previous


def attribute_cache(name: str) -> Dict[int, Tuple[Any, Any]]:
    """`name` の属性 cache。scope が無ければ呼び出し 1 回限りの dict。"""

    caches = getattr(_LOCAL, "caches", None)
    if caches is None:
        return {}
    cache = caches.get(name)
    if cache is None:
        cache = {}
        caches[name] = cache
    return cache


def evaluate_attribute(
    root: Any,
    node_fn: Callable[[Any, Callable[[Any], Any]], Any],
    cache: Dict[int, Tuple[Any, Any]],
) -> Any:
    """`node_fn` を反復で評価する。

    `node_fn(node, child)` は子の答えが要るところで `child(sub)` を呼ぶ。まだ
    無ければ driver が `sub` を先に評価してから `node_fn` をもう一度呼ぶので、
    **最後に成功した実行だけ**が答えになる（途中の実行の副作用は無い前提で、
    node_fn は純関数であること）。

    cache は `id(node) -> (node, value)`。値と一緒に node を持つので、`id()` の
    使い回しで別の式の答えを返すことがない（同時に node を生かしておく）。

    子が多い node（branch の多い PHI、引数の多い intrinsic）では「1 個ずつ解いて
    やり直す」が幅の 2 乗になる。予定表（`render_plan.ResolutionSchedule`）が
    切り替えどきを言ってきたら、要求をまとめて集める実行へ切り替える。その実行の
    答えは捨てるので、仮の値が結果に混ざることはない。

    予定・経路・切り替えの規則は **描画 driver と同じ実装**を使う。ここに写すと
    片方だけが直る（実際、閉路判定が scheduled を active と数える同じ誤りが
    両方にあった）。
    """

    hit = cache.get(id(root))
    if hit is not None and hit[0] is root:
        # 覚えている答えは走査の machinery を組まずに返す。1 回の描画で同じ
        # node の幅は何度も訊かれるので、ここが素通りだと反復 driver の
        # 組み立て費用がその回数だけ乗る。
        return hit[1]

    # 予定と経路の管理は描画 driver と同じ実装（`render_plan`）。閉路判定が
    # 何を見るか（= active な祖先だけ）をここに書き写すと、片方だけが直る。
    schedule = ResolutionSchedule(root, key_of=id)
    missing: List[Any] = []

    def child(sub: Any) -> Any:
        entry = cache.get(id(sub))
        if entry is not None and entry[0] is sub:
            return entry[1]
        missing.append(sub)
        raise _NeedValue

    while schedule:
        node = schedule.current()
        entry = cache.get(id(node))
        if entry is not None and entry[0] is node:
            schedule.settle()
            continue
        del missing[:]
        try:
            value = node_fn(node, child)
        except _NeedValue:
            pending = missing
            if schedule.should_collect_requests():
                pending = _collect_values(node, node_fn, cache) or missing
            schedule.need(pending)
            continue
        cache[id(node)] = (node, value)
        schedule.settle()

    return cache[id(root)][1]


def _collect_values(
    node: Any,
    node_fn: Callable[[Any, Callable[[Any], Any]], Any],
    cache: Dict[int, Tuple[Any, Any]],
) -> List[Any]:
    """規則を仮の子の値で一度走らせ、要求された未解決の子をまとめて返す。

    `child()` が 1 個目の欠けで止めるだけだと、branch の多い PHI や引数の多い
    intrinsic で幅の 2 乗になる（1 回の実行で 1 個しか進まない）。描画 driver と
    同じ規則で、数回で終わらなければまとめて集める実行へ切り替える。

    仮の値で走らせた答えは **捨てる**。採用されるのは本物の値だけで揃った実行
    の答えなので、仮の値が結果に混ざることはない。規則は `all()` / `any()` で
    途中打ち切りすることがあるので、偽・真の両方の仮の値で走らせて、どちらの
    側の子も見落とさないようにする。仮の値は本番では起きない失敗を起こせる
    ので、型の合わない演算などは無視していつもの 1 個ずつの経路へ戻す。閉路と
    契約違反はここで握らない。
    """

    collected: List[Any] = []
    seen: set = set()

    for neutral in (0, 1):

        def collect(sub: Any, _neutral=neutral) -> Any:
            entry = cache.get(id(sub))
            if entry is not None and entry[0] is sub:
                return entry[1]
            if id(sub) not in seen:
                seen.add(id(sub))
                collected.append(sub)
            return _neutral

        try:
            node_fn(node, collect)
        except DISCOVERY_IGNORED_FAILURES:
            pass
        except _NeedValue:  # pragma: no cover - collect never raises it
            pass
    return collected


def iter_expression_nodes(
    expr: Any,
    *,
    include_expression_conditions: bool = False,
) -> List[Any]:
    """式 DAG の distinct node を決定的な順で返す（反復、共有は 1 回だけ）。

    宣言収集（unknown / CALL / float 述語 / global address）が全部これを使う。
    `seen` が無いと共有部分式を親ごとに数え直して指数になる — 収集側が結果を
    dedup していても、走査そのものが終わらない。

    PHI の branch 条件は既定では `Condition.expression` だけを辿る（宣言収集の
    従来の範囲）。条件が `Condition` ではなく式そのもののときにもその式を
    辿りたい走査（「木のどこかに符号比較があるか」）は
    `include_expression_conditions=True` を渡す。走査の範囲は呼び出し側の問い
    によって違うので、既定を勝手に広げて宣言の集合を動かさない。
    """

    if expr is None:
        return []

    nodes: List[Any] = []
    pending: List[Any] = [expr]
    seen: set = set()
    while pending:
        current = pending.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        nodes.append(current)

        expr_type = getattr(current, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is not None and expr_kind is not None and expr_type == expr_kind.PHI and current.value:
            for condition, value in reversed(current.value):
                if value is not None:
                    pending.append(value)
                if condition is None:
                    continue
                condition_expr = getattr(condition, "expression", None)
                if condition_expr is not None:
                    pending.append(condition_expr)
                elif include_expression_conditions and getattr(condition, "expr_type", None) is not None:
                    pending.append(condition)
            continue

        operands = getattr(current, "operands", None) or []
        pending.extend(reversed([operand for operand in operands if operand is not None]))

    return nodes


def any_node(
    expr: Any,
    predicate: Callable[[Any], bool],
    *,
    include_expression_conditions: bool = False,
) -> bool:
    """distinct node のどれかが `predicate` を満たすか（反復、共有は 1 回だけ）。"""

    for node in iter_expression_nodes(
        expr, include_expression_conditions=include_expression_conditions
    ):
        if predicate(node):
            return True
    return False
