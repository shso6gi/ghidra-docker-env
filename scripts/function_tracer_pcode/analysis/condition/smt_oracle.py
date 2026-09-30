# -*- coding: utf-8 -*-
"""SMT-backed reasoning over Condition objects."""

from __future__ import annotations

import importlib
import time
from typing import Any, Dict, Iterable, List, NamedTuple, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
    cache_lookup,
    cache_store,
    clear_condition_caches,
    root_memo,
)
from scripts.function_tracer_pcode.core.budget_policy import (
    FallbackBudgetKind,
    pair_fallback_meter,
)
from scripts.function_tracer_pcode.core.condition_metrics import note, observe
from scripts.function_tracer_pcode.analysis.condition.simplifier_support import (
    note_budget_fallback,
)
from scripts.function_tracer_pcode.analysis.condition.query_identity import (
    QUERY_IDENTITY_SCHEMA,
    RewriteIdentity,
    SolverQueryIdentity,
    runtime_identity_from_projection,
    solver_symbol_identity,
    solver_symbol_identity_is_safe,
)
from scripts.function_tracer_pcode.core import Condition
from scripts.function_tracer_pcode.core.semantic_projection import project_runtime_ref
from scripts.function_tracer_pcode.core.render_smt import (
    CallDeclarationConflict,
    add_call_smt_declaration,
    call_smt_declaration,
    call_smt_declaration_lines,
    collect_float_predicate_smt_declarations,
    collect_unknown_smt_declarations,
    expression_uses_smt_float_theory,
    expression_contains_unsupported_smt_ops,
    expression_returns_bool,
    expression_smt_bit_width,
    smt_logic_name,
)
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
from scripts.function_tracer_pcode.smt.solvers.z3 import isolated_check_end, isolated_solver
from scripts.function_tracer_pcode.core.deadline import (
    NOT_STARTED_FACT,
    ExecutionFact,
    TimeUnit,
    deadline_query,
)

#: Issue #106 PR-106-A: 条件 oracle の問いの checkpoint の stage
CONDITION_ORACLE_STAGE = "condition_oracle"
from scripts.function_tracer_pcode.core.semantic_freeze import publish, validated
from scripts.function_tracer_pcode.core.semantic_snapshot import walk_dag_nodes


class _RootSolverFacts(NamedTuple):
    """root 1 つが script に要求する宣言と、組めるか（root だけに依存する値）。"""

    usable: bool
    symbol_widths: Tuple[Tuple[Any, int], ...] = ()
    memory_widths: frozenset = frozenset()
    call_declarations: Tuple[Tuple[str, Tuple[Tuple[int, ...], int]], ...] = ()
    unknown_decls: frozenset = frozenset()
    float_predicate_decls: frozenset = frozenset()
    uses_float_theory: bool = False


_UNUSABLE_ROOT = _RootSolverFacts(usable=False)


class _QueryFacts(NamedTuple):
    usable: bool
    symbol_widths: Dict[Any, int]
    memory_widths: frozenset
    call_declarations: Dict[str, Tuple[Tuple[int, ...], int]]
    unknown_decls: frozenset
    float_predicate_decls: frozenset
    uses_float_theory: bool


_UNUSABLE_QUERY = _QueryFacts(False, {}, frozenset(), {}, frozenset(), frozenset(), False)


def _root_solver_facts(expr: Any) -> _RootSolverFacts:
    """旧 `_build_script` の条件ごとの検査と宣言の収集（同じ規則、root 1 つ分）。

    node は `walk_dag_nodes`（`SolverQueryIdentity` の root graph と **同じ走査**）から
    読む。symbol の割当（`objvar_<n>`）は graph の symbol から決まるので、幅を集める
    node の集合が別の走査だと、割当があって幅が無い（または逆の）symbol ができる。
    """

    note("oracle.root_facts_built")
    if expr is None:
        return _UNUSABLE_ROOT
    if expression_contains_unsupported_smt_ops(expr, allow_call=True):
        return _UNUSABLE_ROOT
    symbol_widths: Dict[Any, int] = {}
    memory_widths = set()
    call_declarations: Dict[str, Tuple[Tuple[int, ...], int]] = {}
    _graph, nodes = walk_dag_nodes(validated(expr))
    for node in nodes:
        expr_type = getattr(node, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            continue
        if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
            identity = solver_symbol_identity(node)
            if not solver_symbol_identity_is_safe(identity):
                return _UNUSABLE_ROOT
            bit_width = max(1, int(expression_smt_bit_width(node) or 0))
            existing = symbol_widths.get(identity)
            if existing is not None and existing != bit_width:
                return _UNUSABLE_ROOT
            symbol_widths[identity] = bit_width
        elif expr_type == expr_kind.MEMORY:
            mem_bits = max(1, int(expression_smt_bit_width(node) or 0))
            if mem_bits not in {8, 16, 32, 64}:
                return _UNUSABLE_ROOT
            memory_widths.add(mem_bits)
        elif expr_type == expr_kind.CALL:
            # 宣言規則は core/render_smt の共有 helper が唯一の実装。
            # 幅が取れない CALL も、同名で signature が食い違う CALL も
            # fail closed（従来どおり oracle は答えない）。
            try:
                if not add_call_smt_declaration(call_declarations, node):
                    return _UNUSABLE_ROOT
            except CallDeclarationConflict:
                return _UNUSABLE_ROOT
    return _RootSolverFacts(
        usable=True,
        symbol_widths=tuple(symbol_widths.items()),
        memory_widths=frozenset(memory_widths),
        call_declarations=tuple(call_declarations.items()),
        unknown_decls=frozenset(collect_unknown_smt_declarations(expr)),
        float_predicate_decls=frozenset(
            collect_float_predicate_smt_declarations(expr, float_mode="fp")
        ),
        uses_float_theory=bool(expression_uses_smt_float_theory(expr)),
    )


def _merge_root_facts(facts: Iterable[_RootSolverFacts]) -> _QueryFacts:
    """root ごとの値を query 1 つ分へ合わせる（root をまたぐ幅・宣言の食い違いは組めない）。"""

    symbol_widths: Dict[Any, int] = {}
    memory_widths = set()
    call_declarations: Dict[str, Tuple[Tuple[int, ...], int]] = {}
    unknown_decls = set()
    float_predicate_decls = set()
    uses_float_theory = False
    for root in facts:
        if not root.usable:
            return _UNUSABLE_QUERY
        for identity, bit_width in root.symbol_widths:
            existing = symbol_widths.get(identity)
            if existing is not None and existing != bit_width:
                return _UNUSABLE_QUERY
            symbol_widths[identity] = bit_width
        for name, signature in root.call_declarations:
            prior = call_declarations.get(name)
            if prior is not None and prior != signature:
                return _UNUSABLE_QUERY
            call_declarations[name] = signature
        memory_widths.update(root.memory_widths)
        unknown_decls.update(root.unknown_decls)
        float_predicate_decls.update(root.float_predicate_decls)
        uses_float_theory = uses_float_theory or root.uses_float_theory
    return _QueryFacts(
        True,
        symbol_widths,
        frozenset(memory_widths),
        call_declarations,
        frozenset(unknown_decls),
        frozenset(float_predicate_decls),
        uses_float_theory,
    )


def _reason_is_timeout(solver: Any) -> bool:
    """solver の `unknown` が時間切れによるものか（計測用。判定には使わない）。"""

    try:
        reason = str(solver.reason_unknown())
    except (AttributeError, TypeError, ValueError, RuntimeError):
        return False
    return "timeout" in reason or "canceled" in reason


class ConditionSMTOracle:
    """Direct SMT reachability oracle over object-centric condition ASTs.

    Issue #105 PR-105-A: 1 回の問い合わせは

    1. `SolverQueryIdentity.from_conditions`（script を組まない。root ごとの graph は
       pair の cache scope の中で root 1 つにつき 1 回だけ作る）
    2. identity の意味で使えない query（非対応の演算・symbol の identity 不足・幅の食い
       違い）は solver を呼ばずに `None`（覚えない）
    3. 判定の cache を identity で引く（bucket → 完全比較）。**記憶した `None` も hit**
       で、solver を呼び直さない（未判定のまま返す。`True` / `False` にはしない）
    4. miss のときだけ、pair の query 予算（Issue #105 PR-105-B、`oracle_queries`）が
       残っていれば script を組み（symbol は identity の canonical な割当）、solver を
       呼び、判定（`True` / `False` / `None`）を覚える。例外・限界は覚えない
    5. 予算が尽きていれば solver を呼ばずに `None`（oracle 無し相当）。覚えない

    の順。cache の保存と寿命は `condition_cache`、計測は `condition_metrics`、予算の
    上限と pair あたりの消費は `core/budget_policy` が持つ。予算を 1 つ使うのは solver へ
    query を発行する地点だけ（`oracle.queries` と同じ単位。cache hit は使わない）。
    """

    #: query 予算が尽きた記録の site
    QUERY_BUDGET_SITE = "smt_oracle.conjunction_is_unsat"

    QUERY_TIMEOUT_MS = 250
    #: 判定の表の上限（件数。重みの上限と合わせて古い順に捨てる: `condition_cache`）
    _CACHE_LIMIT = 4096
    #: 書き換えの表の上限（件数）
    _REWRITE_CACHE_LIMIT = 8192
    _availability_checked = False
    _available = False
    _z3: Any = None
    _CACHE_KEY_SCHEMA_VERSION = QUERY_IDENTITY_SCHEMA
    #: pair の cache store 上の表の名前（この owner が使う表）
    VERDICT_TABLE = "oracle.verdict"
    REWRITE_TABLE = "oracle.rewrite"
    ROOT_FACTS_MEMO = "oracle.root_facts"
    @classmethod
    def is_available(cls) -> bool:
        if cls._availability_checked:
            return cls._available
        cls._availability_checked = True
        try:
            cls._z3 = importlib.import_module("z3")
            cls._available = True
        except Exception:
            cls._z3 = None
            cls._available = False
        return cls._available

    @classmethod
    def reset_caches(cls) -> None:
        """今の pair の store から、この owner の表を消す（pair 境界の scope とは別に使える）。"""

        clear_condition_caches((cls.VERDICT_TABLE, cls.REWRITE_TABLE))

    @classmethod
    def conjunction_is_unsat(
        cls,
        conditions: Sequence,
        *,
        use_cache: bool = True,
    ) -> Optional[bool]:
        conditions = tuple(conditions or ())
        if conditions and not cls.is_available():
            return None
        query = SolverQueryIdentity.from_conditions(conditions)
        if conditions and not cls._query_facts(query, conditions).usable:
            note("oracle.unusable")
            return None

        # 覚えてよい query か（比較できない graph を含まないか）は表が key の型で判定する
        if use_cache:
            found, cached = cache_lookup(cls.VERDICT_TABLE, query, limit=cls._CACHE_LIMIT)
            if found:
                if cached is None:
                    note("oracle.unknown_hit")
                return cached

        budget = pair_fallback_meter(FallbackBudgetKind.ORACLE_QUERIES)
        if budget.exhausted:
            # 尽きた後は script も組まない（solver を呼ばない。`None` は覚えない）。尽きたままなので
            # 答えは呼ばれ方に依らない（上位の答えは覚えてよい: `simplifier_support`）
            note_budget_fallback(
                budget, site=cls.QUERY_BUDGET_SITE, fallback_taken="oracle_none", history_dependent=False
            )
            return None

        usable, script = cls._build_script(conditions, query=query, use_cache=use_cache)
        if not usable or script is None:
            return None

        z3 = cls._z3
        if z3 is None and not cls.is_available():
            return None
        z3 = cls._z3

        try:
            # Issue #106 PR-106-A: 問いを始める境界。期限を過ぎていれば発行しない（限界を
            # raise）。実行の窓（終わりと、期限が時間を決めたか）はこの実行を始める瞬間に求め、
            # z3 の timeout（ミリ秒）はその窓までに切る（規則と丸めは `core.deadline`）
            configured = cls.QUERY_TIMEOUT_MS / 1000.0
            query_deadline = deadline_query(CONDITION_ORACLE_STAGE)
            if not query_deadline.begin(configured, TimeUnit.MILLISECONDS):
                return None
            window = query_deadline.bound.window(configured, TimeUnit.MILLISECONDS)
            timeout_ms = (
                None if window is None
                else window.timeout(configured, TimeUnit.MILLISECONDS, now=query_deadline.bound.now())
            )
            if window is None or timeout_ms is None:
                query_deadline.settle([NOT_STARTED_FACT])
                return None
            # Issue #161: query ごとに専用の solver context（他の query の履歴を持ち込まない）
            solver = isolated_solver(z3, script, timeout_ms)
            # 予算を 1 つ使うのは発行の直前（`oracle.queries` と同じ地点）
            if not budget.take():
                note_budget_fallback(
                    budget, site=cls.QUERY_BUDGET_SITE, fallback_taken="oracle_none", history_dependent=False
                )
                return None
            note("oracle.queries")
            started = time.monotonic()
            result = solver.check()
            elapsed = time.monotonic() - started
            observe("oracle.check_ms", int(elapsed * 1000))
            # 返った直後: 期限を過ぎていれば・期限が決めた上限で止まったなら答えを採らない
            # （覚えもしない）。上限の前に返った unknown は通常の unknown のまま
            query_deadline.settle([
                ExecutionFact(
                    end=isolated_check_end(
                        z3, result, solver, remaining_seconds=timeout_ms / 1000.0 - elapsed,
                    ),
                    limited=window.limited,
                )
            ])
            if result == z3.unsat:
                verdict: Optional[bool] = True
            elif result == z3.sat:
                verdict = False
            else:
                verdict = None
                note("oracle.unknowns")
                if _reason_is_timeout(solver):
                    note("oracle.timeouts")
            if use_cache:
                cache_store(cls.VERDICT_TABLE, query, verdict, limit=cls._CACHE_LIMIT)
            return verdict
        except AnalysisLimitation:
            # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
            # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
            raise
        except Exception:
            # 例外は判定ではないので覚えない（次の同じ query はもう一度 solver を呼ぶ）
            return None

    @classmethod
    def _query_facts(cls, query: SolverQueryIdentity, conditions: Sequence) -> "_QueryFacts":
        """query を組むのに要る宣言と、組めるか（root ごとの値を root 単位で memo して合わせる）。"""

        return _merge_root_facts(
            root_memo(
                cls.ROOT_FACTS_MEMO,
                getattr(conditions[index], "expression", None),
                _root_solver_facts,
            )
            for index in query.order
        )

    @classmethod
    def _build_script(
        cls,
        conditions: Sequence,
        *,
        query: Optional[SolverQueryIdentity] = None,
        use_cache: bool = True,
    ) -> Tuple[bool, Optional[str]]:
        """SMT script を組む（symbol は `SolverQueryIdentity` の canonical な割当）。

        assert は identity の canonical な順に並べるので、同じ identity の query は
        必ず同じ script になる。書き換え（symbol 名の差し替え）と描画は `RewriteIdentity`
        を key に pair の中で使い回す（`use_cache=False` なら毎回作り直す）。
        """

        if not conditions:
            return True, "(set-logic QF_AUFBV)"
        if not cls.is_available():
            return False, None
        conditions = tuple(conditions)
        if query is None:
            query = SolverQueryIdentity.from_conditions(conditions)
        facts = cls._query_facts(query, conditions)
        if not facts.usable:
            return False, None
        symbol_names = query.symbol_names
        if set(symbol_names) != set(facts.symbol_widths):
            # 割当のある symbol と幅を集めた symbol は同じ走査から来るので一致するはず。
            # 食い違うなら宣言の無い（または使われない）symbol を含む script になるので組まない
            note("oracle.symbol_set_mismatch")
            return False, None
        note("oracle.scripts_built")

        mapping = query.mapping_items()
        lines: List[str] = [
            f"(set-logic {smt_logic_name(uses_float_theory=facts.uses_float_theory, uses_arrays=True, uses_uf=bool(facts.float_predicate_decls))})"
        ]
        for identity, symbol in mapping:
            lines.append(f"(declare-const {symbol} (_ BitVec {facts.symbol_widths[identity]}))")
        for mem_bits in sorted(facts.memory_widths):
            lines.append(
                f"(declare-const mem{mem_bits} (Array (_ BitVec 64) (_ BitVec {mem_bits})))"
            )
        for symbol_name, bit_width in sorted(facts.unknown_decls):
            lines.append(f"(declare-const {symbol_name} (_ BitVec {bit_width}))")
        lines.extend(sorted(facts.float_predicate_decls))
        lines.extend(call_smt_declaration_lines(facts.call_declarations))
        for entry, index in zip(query.entries, query.order):
            condition = conditions[index]
            assertion = cls._condition_assertion(
                condition, entry.graph, mapping, symbol_names, use_cache=use_cache
            )
            lines.append(f"(assert {assertion})")
        return True, "\n".join(lines)

    @classmethod
    def _condition_assertion(
        cls, condition, root_graph, mapping, symbol_names, *, use_cache: bool = True
    ) -> str:
        """条件 1 つの assert 本体（書き換えと描画は `RewriteIdentity` で使い回す）。

        使い回すのは root を書き換えて描画した式の文字列だけ（root graph + mapping +
        描画文脈で決まる値）。向きと bool 化は従来と同じ順（否定してから bool 化）で
        毎回付ける。
        """

        expr = condition.expression
        key = RewriteIdentity.for_root(root_graph, mapping)
        found, rendered = (False, None)
        if use_cache:
            found, rendered = cache_lookup(
                cls.REWRITE_TABLE, key, limit=cls._REWRITE_CACHE_LIMIT
            )
        if not found:
            rendered = cls._rewrite_expr_with_symbol_names(expr, symbol_names).to_smt(
                float_mode="fp"
            )
            if use_cache:
                cache_store(cls.REWRITE_TABLE, key, rendered, limit=cls._REWRITE_CACHE_LIMIT)
        if getattr(condition, "negated", False):
            rendered = f"(not {rendered})"
        if not expression_returns_bool(expr):
            bits = max(1, int(expression_smt_bit_width(expr) or 0))
            rendered = f"(not (= {rendered} (_ bv0 {bits})))"
        return rendered

    # -- solver symbol identity（規則の owner は `query_identity`。ここは委譲だけ） --

    @classmethod
    def _identity_is_solver_safe(cls, identity: Optional[Tuple[Any, ...]]) -> bool:
        return solver_symbol_identity_is_safe(identity)

    @classmethod
    def _expression_identity_key(cls, expr) -> Optional[Tuple[Any, ...]]:
        """solver query 用の object identity（`query_identity.solver_symbol_identity`）。"""

        return solver_symbol_identity(expr)

    @classmethod
    def has_object_identity_support(cls, conditions: Sequence) -> bool:
        """Return false when any PARAMETER/VARIABLE cannot be given a stable identity."""
        try:
            for condition in conditions or ():
                expr = getattr(condition, "expression", None)
                if expr is None:
                    return False
                for node in cls._iter_expression_nodes(expr):
                    expr_type = getattr(node, "expr_type", None)
                    expr_kind = getattr(expr_type, "__class__", None)
                    if expr_type is None or expr_kind is None:
                        continue
                    if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
                        identity = cls._expression_identity_key(node)
                        if not cls._identity_is_solver_safe(identity):
                            return False
            return True
        except Exception:
            return False

    @classmethod
    def _runtime_ref_identity(cls, runtime_ref: Any) -> Optional[Tuple[Any, ...]]:
        """生の ref から identity を作る（式を持たない直接呼び出し用）。

        生 object を読むのは投影側（`core/semantic_projection.py` と、loop
        summary ref の schema を持つ `core/loop_lowering_semantics.py`）だけ
        なので、ここでも投影を作ってから同じ規則を適用する。
        """

        if runtime_ref is None:
            return None
        return runtime_identity_from_projection(project_runtime_ref(None, runtime_ref))

    @classmethod
    def _rewrite_expr_with_symbol_names(
        cls,
        expr,
        symbol_names: Dict[Tuple[Any, ...], str],
        active: Optional[set[int]] = None,
        memo: Optional[Dict[int, Any]] = None,
    ):
        """symbol 名を差し替えた query 用の式を作る。**この関数が公開点**。

        外から呼ばれたとき（`active` / `memo` を渡されないとき）が「1 本作り
        終えた」単位なので、そこで公開する。内部の再帰は組み立ての途中なので
        公開しない。
        """
        if expr is None:
            return expr
        if active is None and memo is None:
            return publish(
                cls._rewrite_expr_with_symbol_names(expr, symbol_names, set(), {})
            )
        if active is None:
            active = set()
        if memo is None:
            memo = {}
        expr_id = id(expr)
        if expr_id in memo:
            return memo[expr_id]
        if expr_id in active:
            memo[expr_id] = expr
            return expr
        active.add(expr_id)

        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            memo[expr_id] = expr
            return expr
        if expr_type in {expr_kind.PARAMETER, expr_kind.VARIABLE}:
            identity = cls._expression_identity_key(expr)
            if identity is None:
                memo[expr_id] = expr
                return expr
            symbol = symbol_names.get(identity)
            if symbol is None:
                memo[expr_id] = expr
                return expr
            rewritten_parameter = expr.clone_with(name=symbol)
            memo[expr_id] = rewritten_parameter
            return rewritten_parameter

        cloned_operands = [
                cls._rewrite_expr_with_symbol_names(
                    operand,
                    symbol_names,
                    active,
                    memo,
                )
                for operand in (getattr(expr, "operands", None) or [])
            ]
        cloned_value = None
        if expr_type == expr_kind.PHI and getattr(expr, "value", None):
            cloned_value = []
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond is not None and cond_expr is not None:
                    rewritten_cond = cls._rewrite_expr_with_symbol_names(
                        cond_expr,
                        symbol_names,
                        active,
                        memo,
                    )
                    cond = Condition(rewritten_cond, bool(getattr(cond, "negated", False)))
                cloned_value.append(
                    (
                        cond,
                        cls._rewrite_expr_with_symbol_names(
                            value,
                            symbol_names,
                            active,
                            memo,
                        ),
                    )
                )
            if cloned_value is not None:
                cloned_value = tuple(cloned_value)
        rewritten_expr = expr.clone_with(
            operands=tuple(cloned_operands),
            value=cloned_value if cloned_value is not None else expr.value,
        )
        memo[expr_id] = rewritten_expr
        active.discard(expr_id)
        return rewritten_expr

    @classmethod
    def _collect_call_declaration(
        cls,
        node: Any,
        ) -> Optional[Tuple[str, Tuple[int, ...], int]]:
        """共有 helper への薄い委譲（既存呼び出し元・test のための入口）。"""
        return call_smt_declaration(node)

    @classmethod
    def _iter_expression_nodes(cls, expr) -> Iterable[Any]:
        pending: List[Any] = [expr]
        seen: set[int] = set()
        while pending:
            current = pending.pop()
            if current is None:
                continue
            current_id = id(current)
            if current_id in seen:
                continue
            seen.add(current_id)
            yield current

            expr_type = getattr(current, "expr_type", None)
            expr_kind = getattr(expr_type, "__class__", None)
            if expr_type is None or expr_kind is None:
                continue

            if expr_type == expr_kind.PHI and getattr(current, "value", None):
                for cond, value in reversed(current.value):
                    if value is not None:
                        pending.append(value)
                    cond_expr = getattr(cond, "expression", None) if cond is not None else None
                    if cond_expr is not None:
                        pending.append(cond_expr)
                continue

            for operand in reversed(list(getattr(current, "operands", None) or [])):
                if operand is not None:
                    pending.append(operand)
