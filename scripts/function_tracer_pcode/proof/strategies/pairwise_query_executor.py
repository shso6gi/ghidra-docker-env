# -*- coding: utf-8 -*-
"""Query execution helpers for PairwiseStrategy."""
import copy
import contextvars
import hashlib
import inspect
import weakref
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.proof.formula.witness_domain import fp_parameters, is_nan_bit_pattern
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UnknownRecoveryActionStatus,
)
from scripts.function_tracer_pcode.proof.formula.returns import (
    RETURN_WIDTH_BRIDGE_MISSING_REASON,
    ReturnWidthMismatchError,
    expression_has_unresolved_value,
    require_equal_return_bit_widths,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult
from scripts.function_tracer_pcode.proof.obligations import (
    AttemptCacheEntry,
    AttemptKey,
    GuardOverlapAttempt,
    GuardOverlapExecutionResult,
    GuardOverlapGraph,
    SolverQueryExecutionReceipt,
    canonical_guard_query_digest,
    canonical_guard_query_text,
    guard_seed,
    issue_structural_equality_receipt,
    register_structural_equality_producer,
    status_from_query_result,
)
from scripts.function_tracer_pcode.proof.obligations.guard_overlap import (
    issue_guard_query_execution_artifact,
    register_guard_query_executor,
)
from scripts.function_tracer_pcode.proof.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    build_case_symbol_declarations,
    build_pair_premise_query,
    build_void_return_disequivalence_query,
)
from scripts.function_tracer_pcode.proof.ub.domain import UB_WITNESS_DOMAIN_KEY


class _SealedLoopV2RendererReceiptMeta(type):
    def __setattr__(cls, name: str, value: Any) -> None:
        if getattr(cls, "_sealed_renderer_receipt_type", False):
            raise TypeError("loop v2 renderer receipt type is immutable")
        super().__setattr__(name, value)

    def __delattr__(cls, name: str) -> None:
        if getattr(cls, "_sealed_renderer_receipt_type", False):
            raise TypeError("loop v2 renderer receipt type is immutable")
        super().__delattr__(name)


@dataclass(frozen=True, init=False)
class RenderedLoopV2SolverQuery(metaclass=_SealedLoopV2RendererReceiptMeta):
    _sealed_renderer_receipt_type = False
    _validator = None
    proof_stage: str
    proof_kind: str
    proof_requirement_id: str
    semantic_target_digest: str
    blocker_target_digest: str
    obligation_id: str
    observation_contract_id: str
    query_text: str
    normalized_assertion_text: str
    premise_assertions: tuple[str, ...]
    declaration_rows: tuple[str, ...]
    source_snapshot_digests: tuple[str, str]
    prepared_surface_digest: str
    execution_identity_digest: str
    renderer_receipt_digest: str

    def __init__(self, **payload: Any) -> None:
        del payload
        raise TypeError("loop v2 renderer receipt must be factory-issued")

    def __copy__(self) -> "RenderedLoopV2SolverQuery":
        return self

    def __deepcopy__(self, memo: Any) -> "RenderedLoopV2SolverQuery":
        return self

    def __reduce_ex__(self, protocol: int) -> Any:
        raise TypeError("loop v2 renderer receipt is not pickle-authority")

    def validate(self) -> None:
        validator = type(self)._validator
        if not callable(validator):
            raise ValueError("loop v2 renderer receipt validator is unavailable")
        validator(self)


@dataclass(frozen=True)
class LoopV2QueryNotFormable:
    """Typed proof-blocker result for a loop-v2 query that cannot be rendered."""

    reason_id: str
    return_size1: Optional[int]
    return_size2: Optional[int]
    detail: str

    def __post_init__(self) -> None:
        if (
            self.reason_id != RETURN_WIDTH_BRIDGE_MISSING_REASON
            or type(self.return_size1) is not int
            or type(self.return_size2) is not int
            or self.return_size1 <= 0
            or self.return_size2 <= 0
            or self.return_size1 == self.return_size2
            or type(self.detail) is not str
            or not self.detail
        ):
            raise ValueError("loop v2 query-not-formable result is invalid")


def _derive_loop_v2_solver_query_payload(
    *, blocker: Any, requirement: Any, analysis1: Any, analysis2: Any,
    case1: Any, case2: Any, pair_id: str, execution_identity_digest: str,
    input_correspondence: Any,
) -> Dict[str, Any]:
    """Derive a loop solver query from the canonical pairwise semantic objects."""

    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
        build_pair_query,
    )
    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
    from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
    from scripts.function_tracer_pcode.authority.contracts import (
        ProofRequirement,
        authority_digest,
        canonical_value,
    )
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LOOP_PRODUCER_STAGE_SPECS,
        LoopBlockerProductionSignal,
        LoopStageCapability,
        _loop_case_object_identity,
    )

    if type(blocker) is not LoopBlockerProductionSignal:
        raise TypeError("loop typed renderer requires exact blocker")
    if type(requirement) is not ProofRequirement:
        raise TypeError("loop typed renderer requires exact proof requirement")
    if type(analysis1) is not FunctionReturnAnalysis or type(
        analysis2
    ) is not FunctionReturnAnalysis:
        raise TypeError("loop typed renderer requires exact function analyses")
    if type(case1) is not ReturnCase or type(case2) is not ReturnCase:
        raise TypeError("loop typed renderer requires exact return cases")
    target_cases = {
        blocker.canonical_target_key[3][1],
        blocker.canonical_target_key[4][1],
    }
    if {
        _loop_case_object_identity(case1),
        _loop_case_object_identity(case2),
    } != target_cases:
        raise ValueError("loop typed renderer cases differ from blocker target")
    left_snapshot = AnalysisSnapshot.from_function_analysis(
        analysis1
    ).semantic_fingerprint
    right_snapshot = AnalysisSnapshot.from_function_analysis(
        analysis2
    ).semantic_fingerprint
    if (
        blocker.canonical_target_key[1][1] != left_snapshot
        or blocker.canonical_target_key[2][1] != right_snapshot
    ):
        raise ValueError("loop typed renderer analyses differ from blocker snapshots")
    matches = tuple(
        row for row in LOOP_PRODUCER_STAGE_SPECS
        if row.proof_kind == requirement.proof_kind
        and row.capability is not LoopStageCapability.STRUCTURAL_ONLY
    )
    if (
        len(matches) != 1
        or requirement.proof_kind != "loop_exact_term_relation"
    ):
        raise ValueError(
            "loop typed pair-value renderer does not own this proof kind"
        )
    # analysis1/2 は prepared surface なので relation を作り直さない（closure が
    # 循環する）。pairwise check が dispatch frame から受け取った最終 relation を使う。
    base_ctx = FormulaBuilder(debug=False).build_base_context(
        analysis1, analysis2, input_correspondence=input_correspondence
    )
    param_replace_fn1 = build_symbol_replacer(
        base_ctx["params1"], base_ctx.get("extra_vars1", []), float_mode="fp", side=1
    )
    param_replace_fn2 = build_symbol_replacer(
        base_ctx["params2"], base_ctx.get("extra_vars2", []), float_mode="fp", side=2
    )
    diagnostic_query_text = build_pair_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    assertion_lines = tuple(
        line.strip() for line in diagnostic_query_text.splitlines()
        if line.strip().startswith("(assert ")
    )
    if not assertion_lines:
        raise ValueError("loop typed renderer produced no semantic assertions")
    if any(not line.endswith(")") for line in assertion_lines):
        raise ValueError("loop typed renderer produced a noncanonical assertion")
    declaration_rows = tuple(
        line.strip() for line in diagnostic_query_text.splitlines()
        if line.strip().startswith("(declare-const ")
    )
    normalized_assertion_text = assertion_lines[-1][len("(assert "):-1]
    premise_assertions = assertion_lines[:-1]
    query_text = "\n".join((
        *declaration_rows,
        *premise_assertions,
        f"(assert {normalized_assertion_text})",
        "(check-sat)",
    ))
    semantic_target_digest = authority_digest({
        "semantic_target": canonical_value(requirement.semantic_target_key),
    })
    payload = {
        "proof_stage": matches[0].proof_stage,
        "proof_kind": requirement.proof_kind,
        "proof_requirement_id": requirement.requirement_id,
        "semantic_target_digest": semantic_target_digest,
        "blocker_target_digest": authority_digest(blocker.canonical_target_key),
        "obligation_id": "loop-obligation-" + authority_digest({
            "blocker_target": blocker.canonical_target_key,
            "proof_kind": requirement.proof_kind,
        })[:32],
        "observation_contract_id": authority_digest(blocker.observation_surface),
        "query_text": query_text,
        "normalized_assertion_text": normalized_assertion_text,
        "premise_assertions": premise_assertions,
        "declaration_rows": declaration_rows,
        "source_snapshot_digests": (left_snapshot, right_snapshot),
        "prepared_surface_digest": authority_digest({
            "left_snapshot": left_snapshot,
            "right_snapshot": right_snapshot,
            "left_case": _loop_case_object_identity(case1),
            "right_case": _loop_case_object_identity(case2),
            "proof_requirement_id": requirement.requirement_id,
            "semantic_target_digest": semantic_target_digest,
        }),
        "execution_identity_digest": execution_identity_digest,
    }
    return payload


def _build_loop_v2_renderer_authority():
    derive = _derive_loop_v2_solver_query_payload
    receipt_type = RenderedLoopV2SolverQuery
    issued: "weakref.WeakValueDictionary[int, RenderedLoopV2SolverQuery]" = (
        weakref.WeakValueDictionary()
    )

    def validate(rendered: RenderedLoopV2SolverQuery) -> None:
        from scripts.function_tracer_pcode.authority.contracts import authority_digest

        payload = {
            name: getattr(rendered, name)
            for name in rendered.__dataclass_fields__
            if name != "renderer_receipt_digest"
        }
        if (
            issued.get(id(rendered)) is not rendered
            or rendered.renderer_receipt_digest != authority_digest(payload)
        ):
            raise ValueError("loop v2 renderer receipt is invalid")

    def render(
        *, blocker: Any, requirement: Any, analysis1: Any, analysis2: Any,
        case1: Any, case2: Any, pair_id: str, execution_identity_digest: str,
        input_correspondence: Any,
    ) -> RenderedLoopV2SolverQuery:
        from scripts.function_tracer_pcode.authority.contracts import authority_digest

        payload = derive(
            blocker=blocker,
            requirement=requirement,
            analysis1=analysis1,
            analysis2=analysis2,
            case1=case1,
            case2=case2,
            pair_id=pair_id,
            execution_identity_digest=execution_identity_digest,
            input_correspondence=input_correspondence,
        )
        rendered = object.__new__(receipt_type)
        for name, value in payload.items():
            object.__setattr__(rendered, name, value)
        object.__setattr__(
            rendered, "renderer_receipt_digest", authority_digest(payload)
        )
        issued[id(rendered)] = rendered
        validate(rendered)
        return rendered

    return render, validate


render_loop_v2_solver_query, _loop_v2_renderer_validator = (
    _build_loop_v2_renderer_authority()
)
type.__setattr__(
    RenderedLoopV2SolverQuery, "_validator", _loop_v2_renderer_validator
)
type.__setattr__(
    RenderedLoopV2SolverQuery, "_sealed_renderer_receipt_type", True
)
del _build_loop_v2_renderer_authority
del _derive_loop_v2_solver_query_payload
del _loop_v2_renderer_validator


def preflight_loop_v2_solver_query(
    *, blocker: Any, requirement: Any, analysis1: Any, analysis2: Any,
    case1: Any, case2: Any, pair_id: str, execution_identity_digest: str,
    input_correspondence: Any,
) -> RenderedLoopV2SolverQuery | LoopV2QueryNotFormable:
    """Render a loop-v2 query or preserve an expected return-width proof gap."""

    try:
        return render_loop_v2_solver_query(
            blocker=blocker,
            requirement=requirement,
            analysis1=analysis1,
            analysis2=analysis2,
            case1=case1,
            case2=case2,
            pair_id=pair_id,
            execution_identity_digest=execution_identity_digest,
            input_correspondence=input_correspondence,
        )
    except ReturnWidthMismatchError as exc:
        if (
            exc.reason_id == RETURN_WIDTH_BRIDGE_MISSING_REASON
            and type(exc.return_size1) is int
            and type(exc.return_size2) is int
            and exc.return_size1 > 0
            and exc.return_size2 > 0
            and exc.return_size1 != exc.return_size2
        ):
            return LoopV2QueryNotFormable(
                reason_id=exc.reason_id,
                return_size1=exc.return_size1,
                return_size2=exc.return_size2,
                detail=str(exc),
            )
        raise


def _build_region_executor_scope():
    current = contextvars.ContextVar("monolithic_region_executor", default=None)

    def run(executor, callback):
        token = current.set(executor)
        try:
            return callback()
        finally:
            current.reset(token)

    def get():
        return current.get()

    return run, get


run_with_region_executor, _current_region_executor = _build_region_executor_scope()


def register_canonical_guard_strategy_type(strategy_type: type) -> None:
    """Register a production strategy type allowed to execute guard queries."""

    global _bind_canonical_guard_strategy_type
    frame = inspect.currentframe()
    caller = frame.f_back if frame is not None else None
    try:
        caller_path = Path(caller.f_code.co_filename) if caller is not None else None
        if (
            caller is None
            or caller.f_code.co_name != "<module>"
            or caller_path is None
            or caller_path.name not in {"pairwise.py", "monolithic.py"}
            or caller_path.parent.name != "strategies"
        ):
            raise RuntimeError("canonical guard strategy registrar is not trusted")
    finally:
        del caller
        del frame
    binder = _bind_canonical_guard_strategy_type
    binder(strategy_type)


def _is_void_return_placeholder(expr: Any) -> bool:
    expr_type = getattr(getattr(expr, "expr_type", None), "name", None)
    return expr_type == "UNKNOWN" and str(getattr(expr, "name", "") or "").lower() == "void"


def _cases_have_void_return_placeholders(case1, case2) -> bool:
    return (
        _is_void_return_placeholder(getattr(case1, "value_expr", None))
        and _is_void_return_placeholder(getattr(case2, "value_expr", None))
    )


def _record_return_width_block(strategy, exc: ReturnWidthMismatchError) -> None:
    stats = getattr(strategy, "_active_normalization_stats", None)
    if stats is None:
        return
    reason_id = getattr(exc, "reason_id", "return_width_bridge_missing")
    stats[reason_id] = int(stats.get(reason_id, 0) or 0) + 1


def solve_query_internal(strategy, query: str, pair_id: str, stage: str = "full", use_hard_timeout: bool = False) -> QueryResult:
    """クエリを実行する"""
    timeout = (
        strategy.per_query_timeout_hard
        if use_hard_timeout
        else getattr(strategy, "_active_query_timeout", strategy.per_query_timeout)
    )
    query_digest = hashlib.sha256(query.encode("utf-8")).hexdigest()
    runner = strategy.solver_runner
    configured_solvers = getattr(runner, "solvers", None)
    if not isinstance(configured_solvers, (tuple, list)):
        configured_solvers = getattr(runner, "_solvers", ())
    if not isinstance(configured_solvers, (tuple, list)):
        configured_solvers = ()
    solver_identity = (
        runner.__class__.__module__,
        runner.__class__.__qualname__,
        tuple(
            getattr(solver, "name", solver.__class__.__qualname__)
            for solver in configured_solvers
        ),
    )
    attempt_key = AttemptKey(
        obligation_instance_id=("logical_smt_query", query_digest, stage),
        producer_id="pairwise.solve_query_internal",
        producer_version="1",
        encoding_version="smtlib-current",
        solver_identity=solver_identity,
        timeout_budget=float(timeout),
        execution_policy=("hard_timeout", bool(use_hard_timeout)),
    )
    cache = getattr(strategy, "_exact_query_attempt_cache", None)
    if cache is not None:
        cached = cache.get(attempt_key)
        if cached is not None and not cached.answers(query):
            # key は query の digest: 文字列の違う query の結果を返さない（#218 PR-D）
            cached = None
        if cached is not None:
            result = copy.copy(cached.outcome)
            result.normalization_rules = list(cached.outcome.normalization_rules)
            source_receipt = getattr(
                result, "solver_query_execution_receipt", None
            )
            if type(source_receipt) is SolverQueryExecutionReceipt:
                result.solver_query_execution_receipt = (
                    source_receipt.for_cache_reuse(
                        query_label=pair_id,
                        proof_stage=stage,
                    )
                )
            result.last_query = query
            strategy._debug_print(
                f"  Pair {pair_id} {stage}: ATTEMPT CACHE HIT "
                f"(query={query_digest[:12]}, t_saved={cached.elapsed_time:.3f}s)"
            )
            stats = getattr(strategy, "_active_normalization_stats", None)
            if stats is not None:
                stats["exact_query_attempt_cache_hits"] = int(
                    stats.get("exact_query_attempt_cache_hits", 0) or 0
                ) + 1
            return result
    shared_region_executor = _current_region_executor()
    parallel_result = (
        shared_region_executor(query, timeout)
        if callable(shared_region_executor)
        else _run_query_with_timeout(strategy.solver_runner, query, timeout=timeout)
    )
    semantic = getattr(parallel_result, "is_equivalent", None)
    if semantic not in {True, False, None}:
        semantic = None
    raw_results = getattr(parallel_result, "results", ())
    if not isinstance(raw_results, (tuple, list)):
        raw_results = ()
    counterexample_raw = None
    if semantic is False:
        counterexample_raw = parallel_result.get_counterexample()

    if semantic is True:
        result_str = "UNSAT"
    elif semantic is False:
        result_str = "SAT"
    else:
        result_str = "UNKNOWN/TIMEOUT"

    elapsed = raw_results[0].elapsed_time if raw_results else 0.0
    strategy._debug_print(f"  Pair {pair_id} {stage}: {result_str} (t={elapsed:.3f}s)")

    _log_solver_errors(strategy, query, raw_results)

    if strategy.save_unknown_queries and semantic is None:
        strategy._save_unknown_query(query, pair_id, stage)

    result = QueryResult(
        is_equivalent=semantic,
        counterexample_raw=counterexample_raw,
        solver_results=parallel_result,
    )
    result.last_query = query
    result.solver_query_execution_receipt = (
        SolverQueryExecutionReceipt.from_execution(
            query=query,
            query_label=pair_id,
            proof_stage=stage,
            parallel_result=parallel_result,
            solver_identity=solver_identity,
            timeout_budget=float(timeout),
            use_hard_timeout=use_hard_timeout,
        )
    )
    if cache is not None:
        cache.put(
            attempt_key,
            AttemptCacheEntry(
                outcome=copy.copy(result),
                query_digest=query_digest,
                query_size=len(query),
                elapsed_time=elapsed,
                retry_eligible=semantic is None,
                query_text=query,
            ),
        )
        stats = getattr(strategy, "_active_normalization_stats", None)
        if stats is not None:
            stats["exact_query_attempt_cache_misses"] = int(
                stats.get("exact_query_attempt_cache_misses", 0) or 0
            ) + 1
    return result


def _build_canonical_guard_query_executor(solver: Any):
    """Close guard authority over the exact canonical solver implementation."""

    trusted_strategy_types: list[type] = []

    def bind_strategy_type(strategy_type: type) -> None:
        if strategy_type in trusted_strategy_types:
            return
        trusted_strategy_types.append(strategy_type)

    def execute(strategy, requirement, query: str, pair_id: str):
        if not any(
            trusted_type in type(strategy).__mro__
            for trusted_type in trusted_strategy_types
        ):
            raise RuntimeError("canonical guard strategy is not trusted")
        runner = getattr(strategy, "solver_runner", None)
        if runner is None:
            raise RuntimeError("canonical guard solver runner is unavailable")
        if (
            canonical_guard_query_digest(query) != requirement.canonical_query_digest
            or canonical_guard_query_text(query) != requirement.canonical_query_text
        ):
            # digest の一致だけで同じ query としない（#218 PR-D）
            raise ValueError("canonical guard query does not match requirement")
        raw = solver(
            strategy,
            query,
            pair_id,
            stage="conds-only",
            use_hard_timeout=False,
        )
        configured_solvers = getattr(runner, "_solvers", ())
        if not isinstance(configured_solvers, (tuple, list)):
            configured_solvers = ()
        solver_identity = (
            runner.__class__.__module__,
            runner.__class__.__qualname__,
            tuple(
                (
                    solver.__class__.__module__,
                    solver.__class__.__qualname__,
                    getattr(solver, "name", solver.__class__.__qualname__),
                )
                for solver in configured_solvers
            ),
        )
        attempt = GuardOverlapAttempt(
            requirement.stable_key(),
            status_from_query_result(raw),
            solver_identity,
            float(getattr(strategy, "per_query_timeout", 0.0) or 0.0),
            requirement.canonical_query_digest,
        )
        query_artifact = issue_guard_query_execution_artifact(
            requirement, attempt, raw
        )
        return GuardOverlapExecutionResult(attempt, raw, query_artifact)

    return execute, bind_strategy_type


(
    execute_canonical_guard_query,
    _bind_canonical_guard_strategy_type,
) = _build_canonical_guard_query_executor(
    solve_query_internal
)
register_guard_query_executor(execute_canonical_guard_query)
del _build_canonical_guard_query_executor


def execute_guard_overlap(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> Any:
    """Execute or reuse one graph node without running value comparison."""
    cond_query = strategy._build_condition_only_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    graph = getattr(strategy, "_guard_overlap_graph", None)
    runtime = getattr(strategy, "_obligation_runtime_session", None)
    if runtime is None and isinstance(graph, GuardOverlapGraph):
        view_id = graph.derived_view_id
        premise_digest = graph.premise_digest
    else:
        view_id = tuple(getattr(getattr(runtime, "current_view", None), "view_id", ()) or ())
        premise_digest = str(getattr(runtime, "premise_digest", "direct-pairwise-premise"))
    if not isinstance(graph, GuardOverlapGraph) or (
        graph.derived_view_id != view_id or graph.premise_digest != premise_digest
    ):
        graph = GuardOverlapGraph(view_id, premise_digest)
        strategy._guard_overlap_graph = graph
    left_seed = guard_seed("left", case1, param_replace_fn1)
    right_seed = guard_seed("right", case2, param_replace_fn2)
    graph_requirement = graph.requirement(left_seed, right_seed, cond_query)

    def plan_guard_query():
        rebuilt = strategy._build_condition_only_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        requirement = _query_requirement(
            "guard_overlap", rebuilt, pair_id, "conds-only"
        )
        def produce_guard_result():
            return execute_canonical_guard_query(
                strategy, graph_requirement, rebuilt, pair_id
            )
        return requirement, "guard_overlap", produce_guard_result

    existing_node = graph.lookup(graph_requirement)
    if existing_node is not None:
        node = existing_node
        stats = getattr(strategy, "_active_normalization_stats", None)
        if stats is not None:
            stats["guard_overlap_graph_hits"] = int(stats.get("guard_overlap_graph_hits", 0) or 0) + 1
    else:
        stage1_requirement, _kind, stage1_producer = plan_guard_query()
        _register_query_replanner(strategy, pair_id, "guard_overlap", plan_guard_query)
        execution_result = _execute_query_obligation(
            strategy,
            stage1_requirement,
            "guard_overlap",
            stage1_producer,
        )
        node = graph.record(execution_result)
        stats = getattr(strategy, "_active_normalization_stats", None)
        if stats is not None:
            stats["guard_overlap_graph_misses"] = int(stats.get("guard_overlap_graph_misses", 0) or 0) + 1
    node.result.raw_result.last_query = cond_query
    node.result.raw_result.pair_stage = "conds-only"
    return node


def solve_query_after_guard(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> QueryResult:
    """Run only the value stage after a precomputed SAT/UNKNOWN guard edge."""
    cond_query = strategy._build_condition_only_query(
        base_ctx, case1, case2, param_replace_fn1, param_replace_fn2, pair_id,
    )

    contextual_unresolved = getattr(strategy, "_case_value_contains_unresolved", None)
    if contextual_unresolved is not None:
        has_unresolved_value = (
            contextual_unresolved(
                case1,
                case2.conditions,
                own_render_fn=param_replace_fn1,
                extra_render_fn=param_replace_fn2,
                base_ctx=base_ctx,
                query_label=f"{pair_id}:value1",
            )
            or contextual_unresolved(
                case2,
                case1.conditions,
                own_render_fn=param_replace_fn2,
                extra_render_fn=param_replace_fn1,
                base_ctx=base_ctx,
                query_label=f"{pair_id}:value2",
            )
        )
    else:
        has_unresolved_value = (
            expression_has_unresolved_value(case1.value_expr)
            or expression_has_unresolved_value(case2.value_expr)
        )

    call_projection_covers_value = bool(
        tuple(
            (base_ctx.get("call_projection_binding_ids_by_pair") or {}).get(
                pair_id,
                (),
            )
            or ()
        )
    )
    if has_unresolved_value and call_projection_covers_value:
        has_unresolved_value = False

    if has_unresolved_value:
        strategy._debug_print(
            f"  Pair {pair_id} with-ineq skipped: unresolved value expression detected"
        )
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["unknown_results"] += 1
        result = QueryResult(is_equivalent=None)
        result.last_query = cond_query
        result.pair_stage = "with-ineq-skipped"
        result.blocking_reason = "unresolved_value_expression"
        result.blocking_detail = "value expression contains UNKNOWN or unsupported SMT operation"
        return result

    if _cases_have_void_return_placeholders(case1, case2):
        required_projection_bindings = tuple(
            (base_ctx.get("call_projection_binding_ids_by_pair") or {}).get(
                pair_id, ()
            )
            or ()
        )
        supporting_solver_receipts = ()
        if required_projection_bindings:
            void_query = build_void_return_disequivalence_query(
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                pair_id,
            )
            result = strategy._solve_query_internal(
                void_query,
                pair_id,
                stage="void-return-projection",
                use_hard_timeout=True,
            )
            result.last_query = void_query
            result.pair_stage = "void-return-projection"
            execution_receipt = getattr(
                result, "solver_query_execution_receipt", None
            )
            if result.is_equivalent is not True:
                return result
            if (
                type(execution_receipt) is not SolverQueryExecutionReceipt
                or not execution_receipt.validates_execution(
                    query=void_query,
                    expected_disposition="unsat",
                    expected_query_label=pair_id,
                )
            ):
                result.is_equivalent = None
                result.blocking_reason = "structural_projection_query_authority_missing"
                result.blocking_detail = (
                    "void-return equality with call projection lacks an exact "
                    "UNSAT execution receipt"
                )
                return result
            supporting_solver_receipts = (execution_receipt,)
        else:
            result = QueryResult(is_equivalent=True)
            result.last_query = cond_query
            result.pair_stage = "void-return"
        result.structural_equality_receipt = (
            issue_structural_equality_receipt(
                query_label=pair_id,
                proof_kind="void-return",
                evidence=(
                    "void-return",
                    hashlib.sha256(cond_query.encode("utf-8")).hexdigest(),
                    int(base_ctx.get("return_size1", 0) or 0),
                    int(base_ctx.get("return_size2", 0) or 0),
                    int(getattr(case1, "index", 0) or 0),
                    int(getattr(case2, "index", 0) or 0),
                ),
                supporting_solver_receipts=supporting_solver_receipts,
            )
        )
        return result

    try:
        require_equal_return_bit_widths(
            base_ctx.get("return_size1", 32),
            base_ctx.get("return_size2", 32),
            context="pairwise value inequality",
        )
    except ReturnWidthMismatchError as exc:
        # 以前はここで usage hint 由来の ``wide == ext(narrow)`` を足した guard
        # query を解いていた。入力 extension 仮定は最終 InputCorrespondence だけが
        # 持てる（Issue #167）。含意される仮定は ``cond_query`` の header premise に
        # 既に入っているので、別の query は作らない。
        strategy._debug_print(f"  Pair {pair_id} with-ineq skipped: {exc}")
        result = QueryResult(is_equivalent=None)
        result.last_query = cond_query
        result.pair_stage = "return-width-mismatch"
        result.blocking_reason = getattr(exc, "reason_id", "return_width_bridge_missing")
        result.blocking_detail = str(exc)
        prepared_observation = (
            (base_ctx.get("return_width_observations_by_pair") or {}).get(pair_id)
        )
        pair_seed = getattr(prepared_observation, "observation_seed", None)
        result.object_target_key = (
            pair_seed.target_id.stable_key()
            if pair_seed is not None
            else ("canonical_return_observation", pair_id)
        )
        bridge_solver = getattr(strategy, "_solve_canonical_return_observation", None)
        runtime = getattr(strategy, "_obligation_runtime_session", None)
        if runtime is not None and callable(bridge_solver):
            def plan_width_bridge_query():
                requirement = ProofRequirementId.create(
                    "value_relation",
                    ("canonical_return_observation", result.object_target_key),
                    ProofRequirementContract(
                        proposition="equal_on_region_after_width_bridge",
                        observation_surface=("return",),
                        active_precondition=(runtime.premise_digest, pair_id),
                    ),
                )

                def produce_width_bridge():
                    bridged = bridge_solver(
                        base_ctx,
                        case1,
                        case2,
                        param_replace_fn1,
                        param_replace_fn2,
                        pair_id,
                        object_target_key=result.object_target_key,
                        blocking_detail=result.blocking_detail,
                    )
                    return bridged if bridged is not None else QueryResult(None)

                return requirement, "value_relation", produce_width_bridge

            runtime.register_target_query_replanner(
                result.object_target_key,
                plan_width_bridge_query,
            )
        result.action_status = UnknownRecoveryActionStatus.PLANNED
        if callable(bridge_solver):
            bridged_result = bridge_solver(
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                pair_id,
                object_target_key=result.object_target_key,
                blocking_detail=result.blocking_detail,
            )
            if bridged_result is not None:
                return bridged_result
            result.proof_requirement_ids = tuple(
                getattr(
                    prepared_observation,
                    "required_proof_requirement_ids",
                    (),
                )
                or ()
            )
            pending_evidence = getattr(
                strategy,
                "_last_canonical_return_width_pending_evidence",
                None,
            )
            if pending_evidence is not None:
                result.object_evidence = pending_evidence
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["unknown_results"] += 1
        _record_return_width_block(strategy, exc)
        return result

    full_query = strategy._build_pair_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    def plan_value_query():
        rebuilt = strategy._build_pair_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        requirement = _query_requirement(
            "value_relation", rebuilt, pair_id, "with-ineq"
        )
        return requirement, "value_relation", lambda: strategy._solve_query_internal(
            rebuilt,
            pair_id,
            stage="with-ineq",
            use_hard_timeout=True,
        )

    stage2_requirement, _kind, stage2_producer = plan_value_query()
    _register_query_replanner(strategy, pair_id, "value_relation", plan_value_query)
    stage2_result = _execute_query_obligation(
        strategy,
        stage2_requirement,
        "value_relation",
        stage2_producer,
        depends_on=(),
    )
    stage2_result.last_query = full_query
    stage2_result.pair_stage = "with-ineq"
    if stage2_result.is_equivalent is False:
        stage2_result = resolve_witness_in_ub_domain(
            strategy, base_ctx, full_query, stage2_result, pair_id,
        )

    if (
        stage2_result.is_equivalent is None
        and getattr(strategy, "enable_solver_proven_rewrite_fallback", False)
    ):
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["solver_proven_rewrite_attempts"] += 1
        rewrite_result = strategy._try_solver_proven_rewrite_equivalence(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        if rewrite_result.is_equivalent is True:
            if getattr(strategy, "_active_normalization_stats", None) is not None:
                strategy._active_normalization_stats["solver_proven_rewrite_successes"] += 1
            return rewrite_result
        if rewrite_result.is_equivalent is False:
            if getattr(strategy, "_active_normalization_stats", None) is not None:
                strategy._active_normalization_stats["solver_proven_rewrite_successes"] += 1
            return rewrite_result
        if getattr(rewrite_result, "blocking_reason", None):
            stage2_result.blocking_reason = rewrite_result.blocking_reason
            stage2_result.blocking_detail = rewrite_result.blocking_detail
            stage2_result.pair_stage = rewrite_result.pair_stage or stage2_result.pair_stage
            stage2_result.evidence_kind = getattr(rewrite_result, "evidence_kind", None)
            stage2_result.object_target_key = getattr(rewrite_result, "object_target_key", None)
            stage2_result.proof_obligation_id = getattr(rewrite_result, "proof_obligation_id", None)
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["solver_proven_rewrite_failures"] += 1

    if (
        stage2_result.is_equivalent is None
        and getattr(strategy, "enable_normalization_fallback", False)
    ):
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["timeout_fallback_attempts"] += 1
        norm_result = strategy._try_normalization_equivalence(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        if norm_result.is_equivalent is True:
            norm_result.pair_stage = "norm-ineq"
            return norm_result
        if norm_result.is_equivalent is False:
            norm_result.pair_stage = "norm-ineq"
            return norm_result
        if getattr(norm_result, "blocking_reason", None):
            stage2_result.blocking_reason = norm_result.blocking_reason
            stage2_result.blocking_detail = norm_result.blocking_detail
            stage2_result.pair_stage = norm_result.pair_stage or stage2_result.pair_stage

    # An undecided solver result carries execution status/receipt only.  A
    # semantic blocker, when present, was established independently above.

    return stage2_result


def resolve_witness_in_ub_domain(
    strategy,
    base_ctx: Dict[str, Any],
    value_query: str,
    sat_result: QueryResult,
    pair_id: str,
) -> QueryResult:
    """SAT の model が反例の領域の外なら、領域の中の model を探し直す（Issue #298）。

    value query は UB の制約を課さない（EQ の前提にしない）ので、model が UB を起こし得る
    入力になることがある。そのまま捨てると、領域の中に正しい witness があっても NOT_EQ を
    失う。value query に反例の領域（両方の関数の全ての演算の制約）を足して
    解き直し、SAT ならその model を witness の候補にする（呼び手は改めて領域・他の検証を
    確かめる）。UNSAT・決まらないときは元の結果を返す（呼び手が witness にしない）。
    UNSAT は EQ の証拠に使わない（制約を上から近似した query なので）。
    """
    if counterexample_ub_domain_status(
        strategy, base_ctx, sat_result.counterexample_raw,
    ) is not False:
        return sat_result
    domain_lines = ub_witness_domain_lines(base_ctx)
    head, sep, tail = value_query.rpartition("(check-sat)")
    if not sep or not domain_lines:
        return sat_result
    domain_query = "\n".join((
        head.rstrip("\n"),
        "; Counterexample domain: no undefined behaviour in either function (Issue #298)",
        *domain_lines,
        sep + tail,
    ))
    stats = getattr(strategy, "_active_normalization_stats", None)
    retried = strategy._solve_query_internal(
        domain_query,
        pair_id,
        stage="with-ineq-ub-domain",
        use_hard_timeout=True,
    )
    found = retried.is_equivalent is False and bool(retried.counterexample_raw)
    if stats is not None:
        key = "ub_witness_domain_resolved" if found else "ub_witness_domain_unresolved"
        stats[key] = stats.get(key, 0) + 1
    if not found:
        return sat_result
    retried.last_query = domain_query
    retried.pair_stage = "with-ineq-ub-domain"
    return retried


def solve_query_twostage(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> QueryResult:
    """Legacy non-authority facade; production uses ``execute_guard_overlap``."""
    cond_query = strategy._build_condition_only_query(
        base_ctx, case1, case2,
        param_replace_fn1, param_replace_fn2, pair_id,
    )

    def plan_guard_query():
        rebuilt = strategy._build_condition_only_query(
            base_ctx, case1, case2,
            param_replace_fn1, param_replace_fn2, pair_id,
        )
        requirement = _query_requirement(
            "guard_overlap", rebuilt, pair_id, "conds-only"
        )
        return requirement, "guard_overlap", lambda: strategy._solve_query_internal(
            rebuilt,
            pair_id,
            stage="conds-only",
            use_hard_timeout=False,
        )

    stage1_requirement, _kind, stage1_producer = plan_guard_query()
    _register_query_replanner(strategy, pair_id, "guard_overlap", plan_guard_query)
    stage1_result = _execute_query_obligation(
        strategy,
        stage1_requirement,
        "guard_overlap",
        stage1_producer,
    )
    if stage1_result.is_equivalent is True:
        stage1_result.last_query = cond_query
        stage1_result.pair_stage = "conds-only"
        return stage1_result
    return solve_query_after_guard(
        strategy, base_ctx, case1, case2,
        param_replace_fn1, param_replace_fn2, pair_id,
    )


def _query_requirement(
    proof_kind: str,
    query: str,
    pair_id: str,
    stage: str,
) -> ProofRequirementId:
    digest = hashlib.sha256(query.encode("utf-8")).hexdigest()
    return ProofRequirementId.create(
        proof_kind,
        ("pair_query", pair_id, stage, digest),
        ProofRequirementContract(
            proposition=proof_kind,
            relation_direction="ordered",
            observation_surface=("return_and_effect",),
            active_precondition=("query_digest", digest),
        ),
    )


def _execute_query_obligation(
    strategy,
    requirement: ProofRequirementId,
    kind: str,
    producer,
    *,
    depends_on=(),
):
    runtime = getattr(strategy, "_obligation_runtime_session", None)
    if runtime is None:
        return producer()
    return runtime.execute(
        requirement,
        kind,
        producer,
        depends_on=depends_on,
    )


def _register_query_replanner(strategy, pair_id, kind, replanner) -> None:
    runtime = getattr(strategy, "_obligation_runtime_session", None)
    if runtime is not None:
        runtime.register_pair_query_replanner(pair_id, kind, replanner)


def validate_counterexample_across_cases(
    strategy,
    base_ctx: Dict[str, Any],
    cases1: Sequence,
    cases2: Sequence,
    param_replace_fn1,
    param_replace_fn2,
    sat_case_indices: Tuple[int, int],
    counterexample_raw: Optional[Dict[str, Any]],
) -> bool:
    """
    SAT 反例が本当に決定的かを、同一モデルで全ケースに対して再検証する。

    同じ入力モデルで:
    - 元の SAT ペアが実際に到達不能なら偽反例
    - 他の到達可能ケース対で値が等しいなら、case split が不完全で偽反例の可能性が高い
    """
    return _validate_counterexample_model(
        strategy,
        base_ctx,
        cases1,
        cases2,
        param_replace_fn1,
        param_replace_fn2,
        counterexample_raw,
        decisive_pairs=[sat_case_indices],
    )


def validate_counterexample_globally(
    strategy,
    base_ctx: Dict[str, Any],
    cases1: Sequence,
    cases2: Sequence,
    param_replace_fn1,
    param_replace_fn2,
    counterexample_raw: Optional[Dict[str, Any]],
) -> bool:
    """
    monolithic SAT 反例が case split 全体で一意に非等価を示すか検証する。

    到達可能な equal pair が 1 つでもあれば、同一モデルが複数の枝割り当てを
    同時に満たしており、反例は曖昧とみなして UNKNOWN へ倒す。
    """
    return _validate_counterexample_model(
        strategy,
        base_ctx,
        cases1,
        cases2,
        param_replace_fn1,
        param_replace_fn2,
        counterexample_raw,
        decisive_pairs=None,
    )


def counterexample_replay_targets(base_ctx: Dict[str, Any]) -> Tuple[Tuple[str, int], ...]:
    """Declared symbols a replay must fix (parameters, extra vars, runtime unknowns)."""

    return tuple(_iter_declared_symbols(base_ctx))


def closed_formula_needs_no_replay(base_ctx: Dict[str, Any]) -> bool:
    """SAT の query そのものを反例としてよいか（replay で固定する記号が無い閉じた式）。

    側ごとの memory の配列は replay の対象に入らない（`smt/witness.py` は配列の sort を除く）ので、配列を読む
    query は閉じた式でも反例にしない（Issue #282, I6: memory の値の実現を確かめていない）。
    """

    return not counterexample_replay_targets(base_ctx) and not base_ctx.get("side_memory_arrays")


def count_counterexample_model_assertions(
    base_ctx: Dict[str, Any],
    counterexample_raw: Optional[Dict[str, Any]],
) -> int:
    if not counterexample_raw:
        return 0
    return len(_build_model_assertions(base_ctx, counterexample_raw))


def build_counterexample_model_assertions(
    base_ctx: Dict[str, Any],
    counterexample_raw: Optional[Dict[str, Any]],
) -> Tuple[str, ...]:
    """Public structured replay seam shared by pairwise and monolithic."""

    return tuple(_build_model_assertions(base_ctx, counterexample_raw))


#: base_ctx の中の、前提の充足可能性の結果（query → 結果。比較の中で共有）
PROOF_PREMISE_STATUS_KEY = "proof_premise_status"


def solve_premise_query(strategy, scope: str, query: str) -> Optional[bool]:
    """前提だけの query を解く: SAT なら True、UNSAT なら False、決まらなければ None。"""
    timeout = max(1, int(getattr(strategy, "per_query_timeout", 5) or 5))
    result = _run_query_with_timeout(strategy.solver_runner, query, timeout=timeout)
    _log_solver_errors(strategy, query, result.results)
    if result.is_equivalent is False:
        return True
    if result.is_equivalent is True:
        return False
    strategy._debug_print(f"  Premise query {scope} returned UNKNOWN/TIMEOUT")
    return None


def require_satisfiable_pair_premises(
    strategy,
    base_ctx: Dict[str, Any],
    cases1,
    cases2,
    param_replace_fn1,
    param_replace_fn2,
) -> None:
    """全ての組の前提（header ∧ 組の追加の assert）が SAT であることを確かめる（Issue #298）。

    pairwise の EQ（全ての組が UNSAT）の直前に呼ぶ。組の UNSAT は guard の query・value
    query・正規化・書き換えのどれから来ても、その組の前提を共有する。前提が UNSAT・判定
    不能なら ``proof.obligations.premise`` が限界を記録して送出する（EQ にしない）。
    """
    from scripts.function_tracer_pcode.proof.obligations.premise import (
        require_satisfiable_premises,
    )

    premises = (
        (
            f"pair({i},{j})",
            build_pair_premise_query(
                base_ctx, case1, case2, param_replace_fn1, param_replace_fn2, f"({i},{j})",
            ),
        )
        for i, case1 in enumerate(cases1)
        for j, case2 in enumerate(cases2)
    )
    solved = require_satisfiable_premises(
        strategy._solve_premise_query,
        premises,
        cache=base_ctx.setdefault(PROOF_PREMISE_STATUS_KEY, {}),
    )
    stats = getattr(strategy, "_active_normalization_stats", None)
    if stats is not None:
        stats["proof_premise_queries"] = int(stats.get("proof_premise_queries", 0) or 0) + solved


def ub_witness_domain_lines(base_ctx: Dict[str, Any]) -> Optional[Tuple[str, ...]]:
    """反例の領域の行（Issue #298）。領域が無効なら ``()``、作れないなら ``None``。

    作れない（描画が式の正確な意味を持たない）ときは、witness が UB を起こさないことを
    示せないので、呼び手は witness にしない。
    """
    from scripts.function_tracer_pcode.core.render_smt import SMT_SEMANTICS_REFUSALS

    domain = base_ctx.get(UB_WITNESS_DOMAIN_KEY)
    if domain is None:
        return ()
    try:
        return tuple(domain.lines())
    except SMT_SEMANTICS_REFUSALS:
        return None


def counterexample_ub_domain_status(
    strategy,
    base_ctx: Dict[str, Any],
    counterexample_raw: Optional[Dict[str, Any]],
) -> Optional[bool]:
    """SAT の model が反例の領域（UB を起こさない入力）に入るか（Issue #298）。

    query は UB の制約を課さない（EQ の前提にしない）。NOT_EQ の witness は、どちらの関数の
    source でも UB を起こさない入力でなければならないが、source の演算・実行条件を binary
    から示せないので、両方の関数の全ての演算の制約を無条件に課す（``proof.ub.domain``）。

    True: 領域に入る（制約が無いときも）。False: 外れる。None: 決まらない（model が無い・
    solver が答えない・領域を作れない）。呼び手は True 以外を witness にしない。
    """
    domain_lines = ub_witness_domain_lines(base_ctx)
    if domain_lines is None:
        return None
    if not any(line.lstrip().startswith("(assert") for line in domain_lines):
        return True
    if counterexample_raw:
        model_assertions = _build_model_assertions(base_ctx, counterexample_raw)
        if not model_assertions:
            return None
    elif closed_formula_needs_no_replay(base_ctx):
        model_assertions = []
    else:
        return None
    lines: List[str] = [
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.append("; Counterexample domain: no undefined behaviour in either function (Issue #298)")
    lines.extend(domain_lines)
    lines.append("(check-sat)")
    return _run_validation_query(strategy, "\n".join(lines), "ub-witness-domain")


def _validate_counterexample_model(
    strategy,
    base_ctx: Dict[str, Any],
    cases1: Sequence,
    cases2: Sequence,
    param_replace_fn1,
    param_replace_fn2,
    counterexample_raw: Optional[Dict[str, Any]],
    decisive_pairs: Optional[Sequence[Tuple[int, int]]],
) -> bool:
    strategy._last_counterexample_rejection_kind = None
    if counterexample_ub_domain_status(strategy, base_ctx, counterexample_raw) is not True:
        # model を NOT_EQ の witness にする経路は全てこの検証を通る（最後の砦）。呼び手は
        # 棄却の種類（``_last_counterexample_rejection_kind``）で理由を選ぶ。
        strategy._last_counterexample_rejection_kind = "ub_domain"
        strategy._debug_print(
            "  Counterexample rejected: model is outside the UB-free input domain"
        )
        return False
    if not counterexample_raw:
        if closed_formula_needs_no_replay(base_ctx):
            # A closed formula (no parameters, no extra or runtime symbols)
            # has nothing to replay: the SAT query itself is the witness.
            return True
        # Otherwise a SAT without a concrete model can never be a validated
        # witness (Issue #28): fail closed.
        strategy._debug_print("  Counterexample rejected: no model to replay")
        return False

    model_assertions = _build_model_assertions(base_ctx, counterexample_raw)
    if not model_assertions:
        strategy._debug_print(
            "  Counterexample rejected: model contains no replay-target declarations"
        )
        return False
    nan_parameters = counterexample_fp_nan_parameters(base_ctx, counterexample_raw)
    if nan_parameters:
        # A witness that only separates the functions on a NaN payload is not
        # evidence of semantic inequivalence: NaN propagation and sign bits are
        # implementation details the benchmarks do not fix (Issue #28).
        strategy._debug_print(
            "  Counterexample rejected: NaN input for floating-point parameter(s) "
            + ", ".join(nan_parameters)
        )
        return False

    feasible_cases1 = _collect_feasible_cases_under_model(
        strategy,
        base_ctx,
        cases1,
        param_replace_fn1,
        model_assertions,
        side_label="function1",
    )
    if feasible_cases1 is None:
        return False
    feasible_cases2 = _collect_feasible_cases_under_model(
        strategy,
        base_ctx,
        cases2,
        param_replace_fn2,
        model_assertions,
        side_label="function2",
    )
    if feasible_cases2 is None:
        return False

    side1_consistent = _feasible_case_values_are_consistent_under_model(
        strategy,
        base_ctx,
        feasible_cases1,
        param_replace_fn1,
        model_assertions,
        return_size=base_ctx.get("return_size1", 32),
        side_label="function1",
    )
    if side1_consistent is None:
        return False
    if not side1_consistent:
        return False
    side2_consistent = _feasible_case_values_are_consistent_under_model(
        strategy,
        base_ctx,
        feasible_cases2,
        param_replace_fn2,
        model_assertions,
        return_size=base_ctx.get("return_size2", 32),
        side_label="function2",
    )
    if side2_consistent is None:
        return False
    if not side2_consistent:
        return False

    decisive_pair_set = set(decisive_pairs or [])
    decisive_pair_feasible = False
    feasible_distinguishing_pair = False

    for i, case1 in enumerate(cases1):
        for j, case2 in enumerate(cases2):
            feasible = _check_pair_feasibility_under_model(
                strategy,
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                model_assertions,
                pair_id=f"({i},{j})",
            )
            if feasible is None:
                strategy._debug_print(
                    f"  Counterexample validation for pair ({i},{j}) was inconclusive"
                )
                return False
            if not feasible:
                continue

            if (i, j) in decisive_pair_set:
                decisive_pair_feasible = True

            equal = _check_pair_equality_under_model(
                strategy,
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                model_assertions,
                pair_id=f"({i},{j})",
            )
            if equal is None:
                strategy._debug_print(
                    f"  Equality re-check for pair ({i},{j}) was inconclusive"
                )
                return False
            if equal:
                strategy._debug_print(
                    f"  Counterexample is ambiguous: model also matches equal pair ({i},{j})"
                )
                return False
            feasible_distinguishing_pair = True

    if decisive_pair_set and not decisive_pair_feasible:
        strategy._debug_print(
            "  Counterexample rejected: original SAT pair is infeasible under the model"
        )
        return False

    if not feasible_distinguishing_pair:
        strategy._debug_print(
            "  Counterexample rejected: no feasible distinguishing case pair under the model"
        )
        return False

    return True


def _collect_feasible_cases_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    cases: Sequence,
    param_replace_fn,
    model_assertions: Sequence[str],
    side_label: str,
) -> Optional[List[Tuple[int, Any]]]:
    feasible_cases: List[Tuple[int, Any]] = []
    for index, case in enumerate(cases):
        feasible = _check_case_feasibility_under_model(
            strategy,
            base_ctx,
            case,
            param_replace_fn,
            model_assertions,
            case_id=f"{side_label}[{index}]",
        )
        if feasible is None:
            strategy._debug_print(
                f"  Counterexample validation for {side_label} case {index} was inconclusive"
            )
            return None
        if feasible:
            feasible_cases.append((index, case))
    return feasible_cases


def _feasible_case_values_are_consistent_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    feasible_cases: Sequence[Tuple[int, Any]],
    param_replace_fn,
    model_assertions: Sequence[str],
    return_size: int,
    side_label: str,
) -> Optional[bool]:
    if len(feasible_cases) < 2:
        return True
    for left_pos, (left_index, left_case) in enumerate(feasible_cases):
        for right_index, right_case in feasible_cases[left_pos + 1 :]:
            equal = _check_same_side_case_equality_under_model(
                strategy,
                base_ctx,
                left_case,
                right_case,
                param_replace_fn,
                model_assertions,
                return_size=return_size,
                pair_id=f"{side_label}[{left_index},{right_index}]",
            )
            if equal is None:
                strategy._debug_print(
                    "  Counterexample validation for "
                    f"{side_label} cases {left_index} and {right_index} was inconclusive"
                )
                return None
            if not equal:
                strategy._debug_print(
                    "  Counterexample is ambiguous: model matches multiple "
                    f"{side_label} return cases with different values "
                    f"({left_index}, {right_index})"
                )
                return False
    return True


def _check_case_feasibility_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case,
    param_replace_fn,
    model_assertions: Sequence[str],
    case_id: str,
) -> Optional[bool]:
    query = _build_single_case_model_validation_query(
        base_ctx,
        case,
        param_replace_fn,
        model_assertions,
    )
    result = _run_validation_query(strategy, query, f"{case_id}:feasible")
    if result is None:
        return None
    return result


def _check_pair_feasibility_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    model_assertions: Sequence[str],
    pair_id: str,
) -> Optional[bool]:
    query = _build_model_validation_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        model_assertions,
        equality=False,
    )
    result = _run_validation_query(strategy, query, f"{pair_id}:feasible")
    if result is None:
        return None
    return result


def _check_pair_equality_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    model_assertions: Sequence[str],
    pair_id: str,
) -> Optional[bool]:
    try:
        query = _build_model_validation_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            model_assertions,
            equality=True,
            pair_id=pair_id,
        )
    except ReturnWidthMismatchError as exc:
        strategy._debug_print(f"  Equality re-check for pair {pair_id} blocked: {exc}")
        return None
    result = _run_validation_query(strategy, query, f"{pair_id}:equal")
    if result is None:
        return None
    return result


def _check_same_side_case_equality_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn,
    model_assertions: Sequence[str],
    return_size: int,
    pair_id: str,
) -> Optional[bool]:
    try:
        query = _build_same_side_case_equality_validation_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn,
            model_assertions,
            return_size=return_size,
        )
    except ReturnWidthMismatchError as exc:
        strategy._debug_print(f"  Same-side equality re-check for {pair_id} blocked: {exc}")
        return None
    result = _run_validation_query(strategy, query, f"{pair_id}:same-side-equal")
    if result is None:
        return None
    return result


def _run_validation_query(strategy, query: str, label: str) -> Optional[bool]:
    timeout = min(getattr(strategy, "per_query_timeout", 5), 5)
    parallel_result = _run_query_with_timeout(strategy.solver_runner, query, timeout=timeout)
    replay_collector = getattr(
        strategy, "_monolithic_replay_execution_collector", None
    )
    if callable(replay_collector):
        replay_collector(query, label, parallel_result)

    _log_solver_errors(strategy, query, parallel_result.results)
    if parallel_result.is_equivalent is True:
        return False
    if parallel_result.is_equivalent is False:
        return True

    strategy._debug_print(f"  Validation query {label} returned UNKNOWN/TIMEOUT")
    return None


def _build_single_case_model_validation_query(
    base_ctx: Dict[str, Any],
    case,
    param_replace_fn,
    model_assertions: Sequence[str],
) -> str:
    lines: List[str] = [
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case, param_replace_fn))
    lines.append("(check-sat)")
    return "\n".join(lines)


def _run_query_with_timeout(solver_runner, query: str, timeout: int):
    """solver_runner.run_sequential(query, timeout=...) をサポートしていれば使う。"""
    run_sequential = getattr(solver_runner, "run_sequential", None)
    if run_sequential is None:
        raise AttributeError("solver_runner has no run_sequential method")

    try:
        signature = inspect.signature(run_sequential)
    except (TypeError, ValueError):
        try:
            return run_sequential(query, timeout=timeout)
        except TypeError as exc:
            if "unexpected keyword argument" in str(exc) and "timeout" in str(exc):
                return run_sequential(query)
            raise

    has_timeout_parameter = "timeout" in signature.parameters
    has_var_keyword = any(
        param.kind == inspect.Parameter.VAR_KEYWORD
        for param in signature.parameters.values()
    )
    if has_timeout_parameter or has_var_keyword:
        try:
            return run_sequential(query, timeout=timeout)
        except TypeError as exc:
            if "unexpected keyword argument" in str(exc) and "timeout" in str(exc):
                return run_sequential(query)
            raise

    return run_sequential(query)


def _build_same_side_case_equality_validation_query(
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn,
    model_assertions: Sequence[str],
    return_size: int,
) -> str:
    value1_smt = case1.get_value_smt(
        param_replace_fn,
        target_bits=return_size,
        use_sign_extension=case1.should_sign_extend_value(),
    )
    value2_smt = case2.get_value_smt(
        param_replace_fn,
        target_bits=return_size,
        use_sign_extension=case2.should_sign_extend_value(),
    )

    lines: List[str] = [
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(build_case_symbol_declarations(
        base_ctx, ((case1, param_replace_fn), (case2, param_replace_fn)),
    ))
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case1, param_replace_fn))
    lines.extend(_build_case_assertions(case2, param_replace_fn))
    lines.extend(
        _build_value_equality_assertions(
            value1_smt,
            value2_smt,
            return_size,
            return_size,
        )
    )
    lines.append("(check-sat)")
    return "\n".join(lines)


def _build_model_validation_query(
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    model_assertions: Sequence[str],
    equality: bool,
    pair_id: Optional[str] = None,
) -> str:
    return_size1 = base_ctx.get("return_size1", 32)
    return_size2 = base_ctx.get("return_size2", 32)
    value1_smt = case1.get_value_smt(
        param_replace_fn1,
        target_bits=return_size1,
        use_sign_extension=case1.should_sign_extend_value(),
    )
    value2_smt = case2.get_value_smt(
        param_replace_fn2,
        target_bits=return_size2,
        use_sign_extension=case2.should_sign_extend_value(),
    )

    if equality and int(return_size1) != int(return_size2):
        prepared = (base_ctx.get("return_width_observations_by_pair") or {}).get(
            str(pair_id or "")
        )
        if not getattr(prepared, "proven", False):
            raise ReturnWidthMismatchError(
                "counterexample replay has no applicable canonical return receipt",
                context="counterexample replay requires original canonical receipt",
                return_size1=return_size1,
                return_size2=return_size2,
            )
        from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
            build_canonical_return_observation_query,
        )
        return build_canonical_return_observation_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            str(pair_id),
            view=prepared.view,
            receipt=prepared.binding_receipt,
            equality=True,
            model_assertions=tuple(model_assertions),
        )

    lines: List[str] = [
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(build_case_symbol_declarations(
        base_ctx, ((case1, param_replace_fn1), (case2, param_replace_fn2)),
    ))
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case1, param_replace_fn1))
    lines.extend(_build_case_assertions(case2, param_replace_fn2))
    if equality:
        lines.extend(
            _build_value_equality_assertions(
                value1_smt,
                value2_smt,
                return_size1,
                return_size2,
            )
        )
    lines.append("(check-sat)")
    return "\n".join(lines)


def _build_case_assertions(
    case,
    param_replace_fn,
) -> List[str]:
    return [f"(assert {cond_str})" for cond_str in case.get_conditions_smt(param_replace_fn)]


def _build_value_equality_assertions(
    value1_smt: str,
    value2_smt: str,
    return_size1: int,
    return_size2: int,
) -> List[str]:
    require_equal_return_bit_widths(
        return_size1,
        return_size2,
        context="counterexample validation value equality",
    )
    return [f"(assert (= {value1_smt} {value2_smt}))"]


def _bit_pattern_is_nan(value: int, bit_width: int) -> bool:
    return is_nan_bit_pattern(value, bit_width)


def counterexample_fp_nan_parameters(
    base_ctx: Dict[str, Any],
    counterexample_raw: Optional[Dict[str, Any]],
) -> Tuple[str, ...]:
    """Names of floating-point parameters the model assigns a NaN bit pattern.

    The rule (which parameters and which bit patterns) is owned by
    `proof.formula.witness_domain`; the formula header declares the same rule as a
    witness preference, so a NaN witness only reaches here when no non-NaN witness
    of the query exists (Issue #161).
    """

    if not counterexample_raw:
        return ()
    names: List[str] = []
    for side in ("params1", "params2"):
        for param in fp_parameters(base_ctx.get(side, []) or []):
            raw_value = counterexample_raw.get(param.smt_name)
            if isinstance(raw_value, bool) or not isinstance(raw_value, int):
                continue
            if is_nan_bit_pattern(raw_value, int(param.bit_width)):
                names.append(param.smt_name)
    return tuple(names)


def _build_model_assertions(base_ctx: Dict[str, Any], counterexample_raw: Dict[str, Any]) -> List[str]:
    declarations = list(_iter_declared_symbols(base_ctx))
    assertions: List[str] = []
    for symbol_name, bit_width in declarations:
        if symbol_name not in counterexample_raw:
            continue
        raw_value = counterexample_raw[symbol_name]
        if not isinstance(raw_value, int):
            continue
        normalized = raw_value % (1 << bit_width)
        assertions.append(f"(assert (= {symbol_name} (_ bv{normalized} {bit_width})))")
    return assertions


def _iter_declared_symbols(base_ctx: Dict[str, Any]) -> Iterable[Tuple[str, int]]:
    for param in base_ctx.get("params1", []):
        yield param.smt_name, param.bit_width
    for param in base_ctx.get("params2", []):
        yield param.smt_name, param.bit_width
    for extra in base_ctx.get("extra_vars1", []):
        yield extra.smt_name, extra.bit_width
    for extra in base_ctx.get("extra_vars2", []):
        yield extra.smt_name, extra.bit_width
    for symbol_name, bit_width in base_ctx.get("runtime_unknown_declarations", []):
        yield symbol_name, bit_width


def _log_solver_errors(strategy, query: str, solver_results) -> None:
    if not solver_results:
        return

    for solver_result in solver_results:
        if solver_result.status != SolverStatus.ERROR:
            continue

        error_msg = solver_result.error_message or ""
        strategy._debug_print(f"  Solver error: {error_msg}")


register_structural_equality_producer(
    "void-return",
    solve_query_after_guard,
)
