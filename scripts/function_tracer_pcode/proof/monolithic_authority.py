"""Fail-closed authority chain for structured monolithic execution.

This module is deliberately independent from ``MonolithicStrategy``.  It owns
the production leases, reconstructs the canonical region census, renders the
expected query with import-time pinned builders, and seals terminal receipts.
The strategy is a consumer of these artifacts; it is not an EQ authority.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import hmac
import inspect
import re
import secrets
from threading import Lock
from typing import Any, Mapping, Optional, Sequence, Tuple
from uuid import uuid4

from scripts.function_tracer_pcode.proof.formula.symbol_replace import (
    build_symbol_replacer as _pinned_symbol_replacer,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    append_ordered_ite_default_case as _pinned_append_default,
    build_condition_only_query as _pinned_guard_renderer,
    build_pair_query as _pinned_value_renderer,
    extract_return_cases as _pinned_extract_cases,
    return_cases_require_relation as _pinned_requires_relation,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    execute_guard_overlap as _pinned_guard_executor,
    solve_query_internal as _pinned_query_executor,
)


_SECRET = secrets.token_bytes(32)
_LOCK = Lock()
_ACTIVE_BRANCHES: set[str] = set()
_ACTIVE_EXECUTIONS: set[str] = set()
_TRUSTED_ROOT_ISSUER_CODES: dict[str, Any] = {}


def _digest(value: Any) -> str:
    return hashlib.sha256(repr(value).encode("utf-8")).hexdigest()


def _seal(payload: Any) -> str:
    return hmac.new(_SECRET, repr(payload).encode("utf-8"), hashlib.sha256).hexdigest()


@dataclass(frozen=True)
class ProductionBranchAuthorityLease:
    lease_id: str
    comparison_session_id: str
    branch_id: str
    generation: int
    runtime_view_digest: str
    seal: str

    @property
    def digest(self) -> str:
        return _digest((self.lease_id, self.comparison_session_id, self.branch_id,
                        self.generation, self.runtime_view_digest, self.seal))

    def validates(self, *, require_active: bool = True) -> bool:
        payload = ("production_branch_authority_v1", self.lease_id,
                   self.comparison_session_id, self.branch_id, self.generation,
                   self.runtime_view_digest)
        valid = hmac.compare_digest(self.seal, _seal(payload))
        if require_active:
            with _LOCK:
                valid = valid and self.lease_id in _ACTIVE_BRANCHES
        return valid


def issue_production_branch_authority(
    comparison_session_id: str,
    branch_id: str,
    generation: int,
    runtime_view_digest: str,
) -> ProductionBranchAuthorityLease:
    caller = inspect.currentframe().f_back
    caller_module = str(caller.f_globals.get("__name__", "")) if caller is not None else ""
    caller_name = str(getattr(caller.f_code, "co_name", "")) if caller is not None else ""
    role = "checker" if (
        caller_module.endswith(".checker.checker")
        and caller_name == "check"
    ) else "stage_runner" if (
        caller_module.endswith(".proof.obligations.stage_runner")
        and caller_name == "execute_branch"
    ) else ""
    if not role:
        raise RuntimeError("production_branch_authority_untrusted_issuer")
    pinned = _TRUSTED_ROOT_ISSUER_CODES.get(role)
    if pinned is not None and pinned is not caller.f_code:
        raise RuntimeError("production_branch_authority_issuer_replaced")
    _TRUSTED_ROOT_ISSUER_CODES.setdefault(role, caller.f_code)
    lease_id = uuid4().hex
    payload = ("production_branch_authority_v1", lease_id,
               comparison_session_id, branch_id, int(generation), runtime_view_digest)
    lease = ProductionBranchAuthorityLease(
        lease_id, comparison_session_id, branch_id, int(generation),
        runtime_view_digest, _seal(payload),
    )
    with _LOCK:
        _ACTIVE_BRANCHES.add(lease_id)
    return lease


def revoke_production_branch_authority(lease: ProductionBranchAuthorityLease) -> None:
    with _LOCK:
        _ACTIVE_BRANCHES.discard(lease.lease_id)


@dataclass(frozen=True)
class MonolithicExecutionAuthorityLease:
    lease_id: str
    parent_digest: str
    comparison_session_id: str
    branch_id: str
    generation: int
    prepared_surface_digest: str
    projection_id: str
    dispatch_nonce: str
    seal: str

    @property
    def digest(self) -> str:
        return _digest((self.lease_id, self.parent_digest, self.comparison_session_id,
                        self.branch_id, self.generation, self.prepared_surface_digest,
                        self.projection_id, self.dispatch_nonce, self.seal))

    def validates(self, parent: ProductionBranchAuthorityLease, *, require_active: bool = True) -> bool:
        payload = ("monolithic_execution_authority_v1", self.lease_id,
                   self.parent_digest, self.comparison_session_id, self.branch_id,
                   self.generation, self.prepared_surface_digest, self.projection_id,
                   self.dispatch_nonce)
        valid = (
            parent.validates(require_active=require_active)
            and self.parent_digest == parent.digest
            and hmac.compare_digest(self.seal, _seal(payload))
        )
        if require_active:
            with _LOCK:
                valid = valid and self.lease_id in _ACTIVE_EXECUTIONS
        return valid


def _verify_parent_lease(
    lease: ProductionBranchAuthorityLease,
    *,
    require_active: bool = True,
) -> bool:
    payload = (
        "production_branch_authority_v1",
        lease.lease_id,
        lease.comparison_session_id,
        lease.branch_id,
        lease.generation,
        lease.runtime_view_digest,
    )
    valid = hmac.compare_digest(lease.seal, _seal(payload))
    if require_active:
        with _LOCK:
            valid = valid and lease.lease_id in _ACTIVE_BRANCHES
    return valid


def _verify_execution_lease(
    execution: MonolithicExecutionAuthorityLease,
    parent: ProductionBranchAuthorityLease,
    *,
    require_active: bool = True,
) -> bool:
    payload = (
        "monolithic_execution_authority_v1",
        execution.lease_id,
        execution.parent_digest,
        execution.comparison_session_id,
        execution.branch_id,
        execution.generation,
        execution.prepared_surface_digest,
        execution.projection_id,
        execution.dispatch_nonce,
    )
    valid = bool(
        _verify_parent_lease(parent, require_active=require_active)
        and execution.parent_digest == parent.digest
        and hmac.compare_digest(execution.seal, _seal(payload))
    )
    if require_active:
        with _LOCK:
            valid = valid and execution.lease_id in _ACTIVE_EXECUTIONS
    return valid


def derive_monolithic_execution_authority(
    parent: ProductionBranchAuthorityLease,
    *,
    prepared_surface_digest: str,
    projection_id: str,
    dispatch_nonce: str,
) -> MonolithicExecutionAuthorityLease:
    if not _verify_parent_lease(parent):
        raise RuntimeError("production_branch_authority_inactive")
    lease_id = uuid4().hex
    payload = ("monolithic_execution_authority_v1", lease_id, parent.digest,
               parent.comparison_session_id, parent.branch_id, parent.generation,
               prepared_surface_digest, projection_id, dispatch_nonce)
    lease = MonolithicExecutionAuthorityLease(
        lease_id, parent.digest, parent.comparison_session_id, parent.branch_id,
        parent.generation, prepared_surface_digest, projection_id, dispatch_nonce,
        _seal(payload),
    )
    with _LOCK:
        _ACTIVE_EXECUTIONS.add(lease_id)
    return lease


def revoke_monolithic_execution_authority(lease: Optional[MonolithicExecutionAuthorityLease]) -> None:
    if lease is not None:
        with _LOCK:
            _ACTIVE_EXECUTIONS.discard(lease.lease_id)


def _case_identity(case: Any) -> Tuple[Any, ...]:
    from scripts.function_tracer_pcode.core.structural import (
        condition_key,
        expression_provenance_key,
    )
    return (
        "monolithic_return_case_v2",
        int(getattr(case, "index", -1)),
        tuple(int(item) for item in tuple(getattr(case, "source_indices", ()) or ())),
        tuple(expression_provenance_key(getattr(case, "value_expr", None))),
        tuple(condition_key(item) for item in tuple(getattr(case, "conditions", ()) or ())),
    )


@dataclass(frozen=True)
class FrozenSurface:
    surface_digest: str
    parent_lease_digest: str
    execution_lease_digest: str
    prepared_surface_digest: str
    generation: int
    left_identity: Tuple[Any, ...]
    right_identity: Tuple[Any, ...]
    seal: str
    analysis1: Any = field(repr=False, compare=False)
    analysis2: Any = field(repr=False, compare=False)
    normalization_settings: Any = field(repr=False, compare=False)

    def validates(self) -> bool:
        payload = ("frozen_monolithic_surface_v2", self.surface_digest,
                   self.parent_lease_digest, self.execution_lease_digest,
                   self.prepared_surface_digest, self.generation,
                   self.left_identity, self.right_identity)
        return hmac.compare_digest(self.seal, _seal(payload))


def freeze_surface(parent, execution, analysis1, analysis2, normalization_settings) -> FrozenSurface:
    if not _verify_execution_lease(execution, parent):
        raise RuntimeError("monolithic_execution_authority_inactive")
    left = tuple(analysis1.outcome_function_identity())
    right = tuple(analysis2.outcome_function_identity())
    surface_digest = _digest(("prepared_monolithic_surface_v1",
                              execution.prepared_surface_digest, left, right))
    payload = ("frozen_monolithic_surface_v2", surface_digest, parent.digest,
               execution.digest, execution.prepared_surface_digest,
               execution.generation, left, right)
    return FrozenSurface(
        surface_digest, parent.digest, execution.digest,
        execution.prepared_surface_digest, execution.generation,
        left, right, _seal(payload), analysis1, analysis2, normalization_settings,
    )


@dataclass(frozen=True)
class CanonicalRegionCensus:
    census_digest: str
    frozen_surface_digest: str
    expected_region_ids: Tuple[str, ...]
    left_case_identities: Tuple[Tuple[Any, ...], ...]
    right_case_identities: Tuple[Tuple[Any, ...], ...]
    seal: str
    cases1: Tuple[Any, ...] = field(repr=False, compare=False)
    cases2: Tuple[Any, ...] = field(repr=False, compare=False)

    def validates(self, frozen: FrozenSurface) -> bool:
        payload = ("canonical_monolithic_census_v1", self.census_digest,
                   self.frozen_surface_digest, self.expected_region_ids,
                   self.left_case_identities, self.right_case_identities)
        return (
            frozen.validates()
            and self.frozen_surface_digest == frozen.surface_digest
            and hmac.compare_digest(self.seal, _seal(payload))
        )


def reconstruct_canonical_census(
    frozen: FrozenSurface,
    _extract_cases=_pinned_extract_cases,
    _requires_relation=_pinned_requires_relation,
    _append_default=_pinned_append_default,
    _identity=_case_identity,
) -> Optional[CanonicalRegionCensus]:
    """Reconstruct independently of the strategy planner."""
    if not _verify_frozen_surface(frozen):
        raise RuntimeError("frozen_monolithic_surface_invalid")
    raw1 = _extract_cases(frozen.analysis1, frozen.normalization_settings,
                          apply_effective_partition=False)
    raw2 = _extract_cases(frozen.analysis2, frozen.normalization_settings,
                          apply_effective_partition=False)
    if not raw1 or not raw2 or _requires_relation(raw1) or _requires_relation(raw2):
        return None
    cases1 = tuple(_append_default(
        frozen.analysis1,
        _extract_cases(frozen.analysis1, frozen.normalization_settings),
    ))
    cases2 = tuple(_append_default(
        frozen.analysis2,
        _extract_cases(frozen.analysis2, frozen.normalization_settings),
    ))
    left_ids = tuple(_identity(case) for case in cases1)
    right_ids = tuple(_identity(case) for case in cases2)
    expected = tuple(f"{left.index}:{right.index}" for left in cases1 for right in cases2)
    census_digest = _digest(("canonical_monolithic_census_v1", frozen.surface_digest,
                             left_ids, right_ids, expected))
    payload = ("canonical_monolithic_census_v1", census_digest, frozen.surface_digest,
               expected, left_ids, right_ids)
    return CanonicalRegionCensus(census_digest, frozen.surface_digest, expected,
                                 left_ids, right_ids, _seal(payload), cases1, cases2)


_SMT_SYMBOL = re.compile(r"(?<![#\w])([A-Za-z_][A-Za-z0-9_.$:-]*)")
_DECL = re.compile(r"^\s*\(declare-(?:fun|const)\s+([^\s()]+)")
_SMT_KEYWORDS = {
    "assert", "check-sat", "get-model", "set-logic", "declare-const",
    "declare-fun", "BitVec", "Bool", "true", "false", "not", "and",
    "or", "xor", "ite", "let", "_", "bvadd", "bvsub", "bvmul",
    "bvand", "bvor", "bvxor", "bvnot", "bvneg", "bvshl", "bvlshr",
    "bvashr", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle",
    "bvsgt", "bvsge", "concat", "extract", "zero_extend", "sign_extend",
}


def _symbols(text: str) -> set[str]:
    return {item for item in _SMT_SYMBOL.findall(text) if item not in _SMT_KEYWORDS}


def _canonical_shared_context(base_ctx: Mapping[str, Any], *, seed_text: str) -> Tuple[dict, str, int]:
    """Soundly remove assertion-only components unrelated to the region.

    Declarations and non-assertion directives remain.  Assertions are retained
    by a symbol-dependency fixed point.  Dropping an independent assertion can
    only enlarge a local region; EQ therefore stays conservative and SAT is
    accepted only after the full-surface replay.
    """
    lines = tuple(dict.fromkeys(str(line) for line in base_ctx.get("header_lines", ())))
    if any(re.sub(r"\s+", " ", line.strip()).lower() == "(assert false)" for line in lines):
        raise RuntimeError("monolithic_untrusted_false_assertion")
    assertions = [line for line in lines if line.lstrip().startswith("(assert ")]
    needed = _symbols(seed_text)
    selected: list[str] = []
    changed = True
    while changed:
        changed = False
        for line in assertions:
            if line in selected:
                continue
            symbols = _symbols(line)
            if symbols & needed or not symbols:
                selected.append(line)
                before = len(needed)
                needed.update(symbols)
                changed = changed or len(needed) != before
    # Declarations are cheap and keeping all of them avoids dialect-specific
    # symbol extraction mistakes.  Duplicate header expressions are shared.
    selected_set = set(selected)
    header = tuple(
        line for line in lines
        if not line.lstrip().startswith("(assert ") or line in selected_set
    )
    ctx = dict(base_ctx)
    ctx["header_lines"] = list(header)
    prelude_digest = hashlib.sha256("\n".join(header).encode("utf-8")).hexdigest()
    removed = sum(len(line) for line in lines) - sum(len(line) for line in header)
    return ctx, prelude_digest, max(0, removed)


@dataclass(frozen=True)
class ExpectedRegionQueryContract:
    contract_digest: str
    census_digest: str
    frozen_surface_digest: str
    execution_lease_digest: str
    region_id: str
    query_kind: str
    formula_digest: str
    shared_prelude_digest: str
    sliced_assertion_bytes: int
    seal: str

    def validates(self, frozen: FrozenSurface, census: CanonicalRegionCensus) -> bool:
        payload = ("expected_region_query_contract_v1", self.contract_digest,
                   self.census_digest, self.frozen_surface_digest,
                   self.execution_lease_digest, self.region_id, self.query_kind,
                   self.formula_digest, self.shared_prelude_digest,
                   self.sliced_assertion_bytes)
        return (
            census.validates(frozen)
            and self.census_digest == census.census_digest
            and self.frozen_surface_digest == frozen.surface_digest
            and self.execution_lease_digest == frozen.execution_lease_digest
            and hmac.compare_digest(self.seal, _seal(payload))
        )


@dataclass(frozen=True)
class RenderedRegionQuery:
    contract: ExpectedRegionQueryContract
    formula: str = field(repr=False)
    render_context: Mapping[str, Any] = field(repr=False, compare=False)

    def validates(self, frozen: FrozenSurface, census: CanonicalRegionCensus) -> bool:
        return (self.contract.validates(frozen, census)
                and hashlib.sha256(self.formula.encode("utf-8")).hexdigest()
                == self.contract.formula_digest)


def render_expected_region_query(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    base_ctx: Mapping[str, Any],
    region_id: str,
    query_kind: str,
    _symbol_replacer=_pinned_symbol_replacer,
    _guard_renderer=_pinned_guard_renderer,
    _value_renderer=_pinned_value_renderer,
    _slice_context=_canonical_shared_context,
) -> RenderedRegionQuery:
    if not _verify_canonical_census(census, frozen) or region_id not in census.expected_region_ids:
        raise RuntimeError("monolithic_region_not_in_canonical_census")
    left_index, right_index = region_id.split(":", 1)
    left = next(case for case in census.cases1 if str(case.index) == left_index)
    right = next(case for case in census.cases2 if str(case.index) == right_index)
    replace1 = _symbol_replacer(base_ctx["params1"], base_ctx.get("extra_vars1", []), float_mode="fp")
    replace2 = _symbol_replacer(base_ctx["params2"], base_ctx.get("extra_vars2", []), float_mode="fp")
    # First render a seed without assertions, then dependency-slice the shared prelude.
    seed_ctx = dict(base_ctx)
    seed_ctx["header_lines"] = []
    renderer = _guard_renderer if query_kind == "guard" else _value_renderer
    if query_kind not in {"guard", "value"}:
        raise RuntimeError("monolithic_query_kind_invalid")
    pair_id = f"monolithic-region-{region_id}"
    seed = renderer(seed_ctx, left, right, replace1, replace2, pair_id)
    sliced_ctx, prelude_digest, removed = _slice_context(base_ctx, seed_text=seed)
    formula = renderer(sliced_ctx, left, right, replace1, replace2, pair_id)
    formula_digest = hashlib.sha256(formula.encode("utf-8")).hexdigest()
    contract_digest = _digest(("expected_region_query_contract_v1", census.census_digest,
                               frozen.surface_digest, frozen.execution_lease_digest,
                               region_id, query_kind, formula_digest, prelude_digest, removed))
    payload = ("expected_region_query_contract_v1", contract_digest,
               census.census_digest, frozen.surface_digest, frozen.execution_lease_digest,
               region_id, query_kind, formula_digest, prelude_digest, removed)
    contract = ExpectedRegionQueryContract(
        contract_digest, census.census_digest, frozen.surface_digest,
        frozen.execution_lease_digest, region_id, query_kind, formula_digest,
        prelude_digest, removed, _seal(payload),
    )
    return RenderedRegionQuery(contract, formula, sliced_ctx)


@dataclass(frozen=True)
class ExpectedRegionQuerySet:
    query_set_digest: str
    frozen_surface_digest: str
    census_digest: str
    ordered_contract_digests: Tuple[str, ...]
    seal: str
    base_ctx: Mapping[str, Any] = field(repr=False, compare=False)
    queries: Tuple[RenderedRegionQuery, ...] = field(repr=False, compare=False)

    def validates(self, frozen: FrozenSurface, census: CanonicalRegionCensus) -> bool:
        payload = (
            "expected_region_query_set_v1",
            self.query_set_digest,
            self.frozen_surface_digest,
            self.census_digest,
            self.ordered_contract_digests,
        )
        return bool(
            census.validates(frozen)
            and self.frozen_surface_digest == frozen.surface_digest
            and self.census_digest == census.census_digest
            and tuple(query.contract.contract_digest for query in self.queries)
            == self.ordered_contract_digests
            and all(query.validates(frozen, census) for query in self.queries)
            and hmac.compare_digest(self.seal, _seal(payload))
        )

    def query(self, region_id: str, query_kind: str) -> RenderedRegionQuery:
        matches = tuple(
            query for query in self.queries
            if query.contract.region_id == region_id
            and query.contract.query_kind == query_kind
        )
        if len(matches) != 1:
            raise RuntimeError("expected_region_query_contract_not_unique")
        return matches[0]


def _verify_frozen_surface(
    frozen: FrozenSurface,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(frozen) is not FrozenSurface:
        return False
    payload = (
        "frozen_monolithic_surface_v2",
        frozen.surface_digest,
        frozen.parent_lease_digest,
        frozen.execution_lease_digest,
        frozen.prepared_surface_digest,
        frozen.generation,
        frozen.left_identity,
        frozen.right_identity,
    )
    return _compare(frozen.seal, _seal_fn(payload))


def _verify_canonical_census(
    census: CanonicalRegionCensus,
    frozen: FrozenSurface,
    _verify_frozen=_verify_frozen_surface,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(census) is not CanonicalRegionCensus:
        return False
    payload = (
        "canonical_monolithic_census_v1",
        census.census_digest,
        census.frozen_surface_digest,
        census.expected_region_ids,
        census.left_case_identities,
        census.right_case_identities,
    )
    return bool(
        _verify_frozen(frozen)
        and census.frozen_surface_digest == frozen.surface_digest
        and _compare(census.seal, _seal_fn(payload))
    )


def _verify_region_query_contract(
    contract: ExpectedRegionQueryContract,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    _verify_census=_verify_canonical_census,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(contract) is not ExpectedRegionQueryContract:
        return False
    payload = (
        "expected_region_query_contract_v1",
        contract.contract_digest,
        contract.census_digest,
        contract.frozen_surface_digest,
        contract.execution_lease_digest,
        contract.region_id,
        contract.query_kind,
        contract.formula_digest,
        contract.shared_prelude_digest,
        contract.sliced_assertion_bytes,
    )
    return bool(
        _verify_census(census, frozen)
        and contract.census_digest == census.census_digest
        and contract.frozen_surface_digest == frozen.surface_digest
        and contract.execution_lease_digest == frozen.execution_lease_digest
        and contract.region_id in census.expected_region_ids
        and contract.query_kind in {"guard", "value"}
        and _compare(contract.seal, _seal_fn(payload))
    )


def _verify_rendered_region_query(
    query: RenderedRegionQuery,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    _verify_contract=_verify_region_query_contract,
    _sha256=hashlib.sha256,
) -> bool:
    if type(query) is not RenderedRegionQuery:
        return False
    return bool(
        _verify_contract(query.contract, frozen, census)
        and _sha256(query.formula.encode("utf-8")).hexdigest()
        == query.contract.formula_digest
    )


def _verify_expected_query_set(
    query_set: ExpectedRegionQuerySet,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    _verify_census=_verify_canonical_census,
    _verify_query=_verify_rendered_region_query,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(query_set) is not ExpectedRegionQuerySet:
        return False
    payload = (
        "expected_region_query_set_v1",
        query_set.query_set_digest,
        query_set.frozen_surface_digest,
        query_set.census_digest,
        query_set.ordered_contract_digests,
    )
    return bool(
        _verify_census(census, frozen)
        and query_set.frozen_surface_digest == frozen.surface_digest
        and query_set.census_digest == census.census_digest
        and tuple(query.contract.contract_digest for query in query_set.queries)
        == query_set.ordered_contract_digests
        and all(
            _verify_query(query, frozen, census)
            for query in query_set.queries
        )
        and _compare(query_set.seal, _seal_fn(payload))
    )


def _query_from_set(
    query_set: ExpectedRegionQuerySet,
    region_id: str,
    query_kind: str,
) -> RenderedRegionQuery:
    matches = tuple(
        query for query in query_set.queries
        if query.contract.region_id == region_id
        and query.contract.query_kind == query_kind
    )
    if len(matches) != 1:
        raise RuntimeError("expected_region_query_contract_not_unique")
    return matches[0]


@dataclass(frozen=True)
class SharedZ3SessionCertificate:
    certificate_digest: str
    query_set_digest: str
    execution_lease_digest: str
    backend_identity: Tuple[str, ...]
    seal: str

    def validates(self, query_set: ExpectedRegionQuerySet, frozen: FrozenSurface) -> bool:
        fields = (
            self.query_set_digest,
            self.execution_lease_digest,
            self.backend_identity,
        )
        return bool(
            self.disposition in {"unsat", "sat", "unknown"}
            and self.query_contract_digest == query.contract.contract_digest
            and self.region_id == query.contract.region_id
            and self.query_kind == query.contract.query_kind
            and self.formula_digest == query.contract.formula_digest
            and self.session_certificate_digest == session_certificate.certificate_digest
            and self.execution_lease_digest == session_certificate.execution_lease_digest
            and self.backend_identity == session_certificate.backend_identity
            and hmac.compare_digest(self.seal, _seal(payload))
        )
        return bool(
            _verify_expected_query_set(
                query_set, frozen, reconstruct_canonical_census(frozen)
            )
            and self.query_set_digest == query_set.query_set_digest
            and self.execution_lease_digest == frozen.execution_lease_digest
            and self.certificate_digest == _digest(("shared_z3_session_v1", *fields))
            and hmac.compare_digest(
                self.seal,
                _seal(("shared_z3_session_v1", self.certificate_digest, *fields)),
            )
        )


class SharedZ3RegionSession:
    """One Z3 context/solver with common assertions installed once.

    Each canonical region formula is parsed into the same Z3 context during
    session construction.  Assertions present in every formula are added once;
    region-local assertions are checked under push/pop.
    """

    def __init__(self, query_set: ExpectedRegionQuerySet, frozen: FrozenSurface) -> None:
        import importlib
        from scripts.function_tracer_pcode.smt.solvers.z3 import prepare_witness_query

        self._z3 = importlib.import_module("z3")
        self._ctx = self._z3.Context()
        parsed: dict[str, Tuple[Any, ...]] = {}
        # Issue #161: canonical witness に要る項（witness の優先・成分）も同じ 1 回の parse
        # で用意する（execute の中で script を読み直さない）
        self._prepared: dict[str, Any] = {}
        sexprs_by_query: list[set[str]] = []
        ast_nodes_by_query: list[set[str]] = []
        for query in query_set.queries:
            prepared = prepare_witness_query(self._z3, query.formula, self._ctx)
            self._prepared[query.contract.formula_digest] = prepared
            assertions = prepared.assertions
            parsed[query.contract.formula_digest] = assertions
            sexprs_by_query.append({item.sexpr() for item in assertions})
            nodes: set[str] = set()
            pending = list(assertions)
            while pending:
                node = pending.pop()
                nodes.add(node.sexpr())
                pending.extend(node.children())
            ast_nodes_by_query.append(nodes)
        common = set.intersection(*sexprs_by_query) if sexprs_by_query else set()
        shared_nodes = (
            set.intersection(*ast_nodes_by_query) if ast_nodes_by_query else set()
        )
        representative: dict[str, Any] = {}
        for assertions in parsed.values():
            for item in assertions:
                representative.setdefault(item.sexpr(), item)
        self._solver = self._z3.Solver(ctx=self._ctx)
        self._solver.add(*(representative[item] for item in sorted(common)))
        self._specific = {
            digest: tuple(item for item in assertions if item.sexpr() not in common)
            for digest, assertions in parsed.items()
        }
        self.parse_count = len(parsed)
        # The context hash-conses these shared nodes even when their enclosing
        # assertions are region-local.  Top-level common assertions are also
        # installed only once in the incremental solver.
        self.shared_ast_count = len(shared_nodes)
        self.shared_assertion_count = len(common)
        self.check_count = 0
        backend_identity = (
            "z3",
            str(self._z3.get_version_string()),
            "SharedZ3RegionSession.execute:v1",
        )
        fields = (query_set.query_set_digest, frozen.execution_lease_digest, backend_identity)
        digest = _digest(("shared_z3_session_v1", *fields))
        self.certificate = SharedZ3SessionCertificate(
            digest,
            *fields,
            _seal(("shared_z3_session_v1", digest, *fields)),
        )

    def execute(self, query: str, timeout: int) -> Any:
        import time
        from scripts.function_tracer_pcode.smt import ParallelResult
        from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
        digest = hashlib.sha256(query.encode("utf-8")).hexdigest()
        if digest not in self._specific:
            raise RuntimeError("shared_z3_region_query_outside_canonical_set")
        from scripts.function_tracer_pcode.smt.execution import ExecutionBudget
        from scripts.function_tracer_pcode.smt.interface import (
            enforce_witness_contract,
            interrupted_result,
        )
        from scripts.function_tracer_pcode.smt.solvers.z3 import sat_result_with_witness
        from scripts.function_tracer_pcode.core.deadline import TimeUnit, deadline_query
        from scripts.function_tracer_pcode.smt.interface import (
            apply_adoption,
            execution_fact,
            not_started_result,
        )
        from scripts.function_tracer_pcode.smt.parallel import SOLVER_STAGE

        started = time.time()
        configured = max(1, int(timeout))
        # Issue #106 PR-106-A: 問いを始める境界（runner の問い合わせと同じ規則）。期限を
        # 過ぎていれば始めない。この実行の窓の終わりが実行の予算の上限になる
        query_deadline = deadline_query(SOLVER_STAGE)
        window = (
            query_deadline.bound.window(configured, TimeUnit.MILLISECONDS)
            if query_deadline.begin(configured) else None
        )
        if window is None:
            item = not_started_result("Z3(shared-region)")
            query_deadline.settle([execution_fact(item)])
            return ParallelResult.from_backend_results(apply_adoption([item], query_deadline.adoption))
        # Issue #161: 実行の状態（期限と中止）は 1 回の実行に 1 つの `ExecutionBudget`。
        # execute の入口で作り、初回の check と canonical witness の生成・SAT の確定がこれに
        # 問う（共有 session には中止の入力が無いので期限だけ）。
        budget = ExecutionBudget.starting_now(configured, not_after=window.adapter_end)
        self._solver.push()
        try:
            self._solver.add(*self._specific[digest])
            stop = budget.interruption()
            if stop is not None:
                item = interrupted_result(
                    "Z3(shared-region)", stop, "the execution stopped before the check",
                    time.time() - started,
                )
                item.deadline_limited = window.limited
                query_deadline.settle([execution_fact(item)])
                return ParallelResult.from_backend_results(apply_adoption([item], query_deadline.adoption))
            self._solver.set(timeout=budget.timeout_ms())
            verdict = self._solver.check()
            elapsed = time.time() - started
            self.check_count += 1
            if verdict == self._z3.sat:
                # 共有 session の履歴（先に解いた region）に依らない canonical witness。
                # 確定の手順（生成の前後の中断確認）は interface が持つ。
                item = sat_result_with_witness(
                    self._z3, self._solver, self._prepared[digest],
                    solver_name="Z3(shared-region)", started=started, budget=budget,
                )
            elif verdict == self._z3.unsat:
                item = SolverResult("Z3(shared-region)", SolverStatus.UNSAT,
                                    elapsed_time=elapsed)
            else:
                reason = str(self._solver.reason_unknown())
                stop = budget.interruption_after_unknown(reason)
                if stop is not None:
                    item = interrupted_result("Z3(shared-region)", stop, reason, elapsed)
                else:
                    item = SolverResult("Z3(shared-region)", SolverStatus.UNKNOWN,
                                        elapsed_time=elapsed, error_message=reason,
                                        cause=budget.unknown_end(reason))
            # 1 query × 1 backend の結果: 契約を境界で検査し、backend 集約の規則で包む
            item = enforce_witness_contract(item, query, canonical=True)
        finally:
            self._solver.pop()
        # 返った直後（共有 solver を元の assertion に戻した後）: 期限を過ぎていれば・期限で
        # 切られていれば採らない
        item.deadline_limited = window.limited
        query_deadline.settle([execution_fact(item)])
        return ParallelResult.from_backend_results(apply_adoption([item], query_deadline.adoption))

def create_shared_z3_region_session(
    query_set: ExpectedRegionQuerySet,
    frozen: FrozenSurface,
) -> SharedZ3RegionSession:
    return SharedZ3RegionSession(query_set, frozen)


_PINNED_SHARED_Z3_EXECUTE = SharedZ3RegionSession.execute
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    run_with_region_executor as _PINNED_RUN_WITH_REGION_EXECUTOR,
)
_REGION_RECEIPT_ISSUER = object()


def build_expected_region_query_set(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    base_ctx: Mapping[str, Any],
    _renderer=render_expected_region_query,
    _verify_census=_verify_canonical_census,
    _verify_query_set=_verify_expected_query_set,
) -> ExpectedRegionQuerySet:
    if not _verify_census(census, frozen):
        raise RuntimeError("canonical_monolithic_census_invalid")
    queries = tuple(
        _renderer(frozen, census, base_ctx, region_id, query_kind)
        for region_id in census.expected_region_ids
        for query_kind in ("guard", "value")
    )
    ordered = tuple(query.contract.contract_digest for query in queries)
    query_set_digest = _digest((
        "expected_region_query_set_v1",
        frozen.surface_digest,
        census.census_digest,
        ordered,
    ))
    payload = (
        "expected_region_query_set_v1",
        query_set_digest,
        frozen.surface_digest,
        census.census_digest,
        ordered,
    )
    result = ExpectedRegionQuerySet(
        query_set_digest,
        frozen.surface_digest,
        census.census_digest,
        ordered,
        _seal(payload),
        dict(base_ctx),
        queries,
    )
    if not _verify_query_set(result, frozen, census):
        raise RuntimeError("expected_region_query_set_invalid")
    return result


@dataclass(frozen=True)
class RegionSolverExecutionReceipt:
    receipt_digest: str
    query_contract_digest: str
    region_id: str
    query_kind: str
    formula_digest: str
    disposition: str
    solver_result_digest: str
    session_certificate_digest: str
    execution_lease_digest: str
    backend_identity: Tuple[str, ...]
    seal: str

    def validates(
        self,
        query: RenderedRegionQuery,
        session_certificate: SharedZ3SessionCertificate,
    ) -> bool:
        pass


def _verify_session_certificate(
    certificate: SharedZ3SessionCertificate,
    query_set: ExpectedRegionQuerySet,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    _verify_query_set=_verify_expected_query_set,
    _digest_fn=_digest,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(certificate) is not SharedZ3SessionCertificate:
        return False
    fields = (
        certificate.query_set_digest,
        certificate.execution_lease_digest,
        certificate.backend_identity,
    )
    return bool(
        _verify_query_set(query_set, frozen, census)
        and certificate.query_set_digest == query_set.query_set_digest
        and certificate.execution_lease_digest == frozen.execution_lease_digest
        and certificate.certificate_digest == _digest_fn(("shared_z3_session_v1", *fields))
        and _compare(
            certificate.seal,
            _seal_fn(("shared_z3_session_v1", certificate.certificate_digest, *fields)),
        )
    )


def _verify_region_execution_receipt(
    receipt: RegionSolverExecutionReceipt,
    query: RenderedRegionQuery,
    certificate: SharedZ3SessionCertificate,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(receipt) is not RegionSolverExecutionReceipt:
        return False
    payload = (
        "region_solver_execution_receipt_v1",
        receipt.receipt_digest,
        receipt.query_contract_digest,
        receipt.region_id,
        receipt.query_kind,
        receipt.formula_digest,
        receipt.disposition,
        receipt.solver_result_digest,
        receipt.session_certificate_digest,
        receipt.execution_lease_digest,
        receipt.backend_identity,
    )
    return bool(
        receipt.disposition in {"unsat", "sat", "unknown"}
        and receipt.query_contract_digest == query.contract.contract_digest
        and receipt.region_id == query.contract.region_id
        and receipt.query_kind == query.contract.query_kind
        and receipt.formula_digest == query.contract.formula_digest
        and receipt.session_certificate_digest == certificate.certificate_digest
        and receipt.execution_lease_digest == certificate.execution_lease_digest
        and receipt.backend_identity == certificate.backend_identity
        and _compare(receipt.seal, _seal_fn(payload))
    )
def _solver_disposition(result: Any) -> str:
    value = getattr(result, "is_equivalent", None)
    return "unsat" if value is True else "sat" if value is False else "unknown"


def _solver_result_digest(result: Any) -> str:
    return _digest((
        "solver_result_v1",
        getattr(result, "is_equivalent", None),
        tuple(
            (
                str(getattr(item, "solver_name", "")),
                str(getattr(getattr(item, "status", None), "value", getattr(item, "status", ""))),
                str(getattr(item, "error_message", "") or ""),
            )
            for item in tuple(getattr(result, "results", ()) or ())
        ),
    ))


def _issue_region_execution_receipt(
    query: RenderedRegionQuery,
    solver_result: Any,
    session_certificate: SharedZ3SessionCertificate,
    issuer: Any,
) -> RegionSolverExecutionReceipt:
    if issuer is not _REGION_RECEIPT_ISSUER:
        raise RuntimeError("region_solver_receipt_issuer_not_authorized")
    disposition = _solver_disposition(solver_result)
    result_digest = _solver_result_digest(solver_result)
    fields = (
        query.contract.contract_digest,
        query.contract.region_id,
        query.contract.query_kind,
        query.contract.formula_digest,
        disposition,
        result_digest,
        session_certificate.certificate_digest,
        session_certificate.execution_lease_digest,
        session_certificate.backend_identity,
    )
    receipt_digest = _digest(("region_solver_execution_receipt_v1", *fields))
    payload = ("region_solver_execution_receipt_v1", receipt_digest, *fields)
    return RegionSolverExecutionReceipt(receipt_digest, *fields, _seal(payload))


def execute_expected_guard_query(
    strategy: Any,
    rendered: RenderedRegionQuery,
    left: Any,
    right: Any,
    replace1: Any,
    replace2: Any,
    pair_id: str,
    session: SharedZ3RegionSession,
    _execute=_PINNED_SHARED_Z3_EXECUTE,
    _run_in_scope=_PINNED_RUN_WITH_REGION_EXECUTOR,
) -> Tuple[Any, RegionSolverExecutionReceipt]:
    executor = lambda query, timeout: _execute(session, query, timeout)
    node = _run_in_scope(
        executor,
        lambda: _pinned_guard_executor(
            strategy, rendered.render_context, left, right, replace1, replace2, pair_id
        ),
    )
    if str(node.result.raw_result.last_query or "") != rendered.formula:
        raise RuntimeError("monolithic_guard_render_contract_mismatch")
    return node, _issue_region_execution_receipt(
        rendered, node.result.raw_result, session.certificate, _REGION_RECEIPT_ISSUER
    )


def execute_expected_value_query(
    strategy: Any,
    rendered: RenderedRegionQuery,
    pair_id: str,
    session: SharedZ3RegionSession,
    _execute=_PINNED_SHARED_Z3_EXECUTE,
    _run_in_scope=_PINNED_RUN_WITH_REGION_EXECUTOR,
) -> Tuple[Any, RegionSolverExecutionReceipt]:
    executor = lambda query, timeout: _execute(session, query, timeout)
    result = _run_in_scope(
        executor,
        lambda: _pinned_query_executor(
            strategy, rendered.formula, pair_id, stage="monolithic-region-value"
        ),
    )
    if hashlib.sha256(rendered.formula.encode("utf-8")).hexdigest() != rendered.contract.formula_digest:
        raise RuntimeError("monolithic_value_render_contract_mismatch")
    return result, _issue_region_execution_receipt(
        rendered, result, session.certificate, _REGION_RECEIPT_ISSUER
    )


@dataclass(frozen=True)
class MonolithicProofVerificationBundle:
    bundle_digest: str
    frozen_surface_digest: str
    census_digest: str
    query_set_digest: str
    execution_receipt_digests: Tuple[str, ...]
    record_digests: Tuple[str, ...]
    outcome_kind: str
    seal: str
    frozen: FrozenSurface = field(repr=False, compare=False)
    census: CanonicalRegionCensus = field(repr=False, compare=False)
    query_set: ExpectedRegionQuerySet = field(repr=False, compare=False)
    execution_receipts: Tuple[RegionSolverExecutionReceipt, ...] = field(repr=False, compare=False)
    query_records: Tuple[Any, ...] = field(repr=False, compare=False)
    session_certificate: SharedZ3SessionCertificate = field(repr=False, compare=False)


@dataclass(frozen=True)
class LegacyMonolithicCounterexampleProofBundle:
    """Proof authority for a fixed-model whole-surface legacy fallback."""

    bundle_digest: str
    frozen_surface_digest: str
    census_digest: str
    legacy_replay_receipt_digest: str
    whole_surface_replay_receipt_digest: str
    outcome_kind: str
    seal: str
    frozen: FrozenSurface = field(repr=False, compare=False)
    census: CanonicalRegionCensus = field(repr=False, compare=False)
    legacy_replay_receipt: Any = field(repr=False, compare=False)
    whole_surface_replay_receipt: Any = field(repr=False, compare=False)


def _record_digest(record: Any, _digest_fn=_digest) -> str:
    return _digest_fn(("query_execution_record_v2",
        (type(record).__module__, type(record).__qualname__, id(type(record))),
        str(getattr(record, "query_label", "")),
        str(getattr(record, "premise_digest", "")),
        str(getattr(record, "formula_digest", "")),
        str(getattr(record, "disposition", "")),
        str(getattr(record, "proof_kind", "")),
        tuple(getattr(record, "projection_binding_ids", ()) or ()),
        str(getattr(record, "formula_text", "")),
        str(getattr(record, "return_width_observation_view_digest", "")),
        str(getattr(record, "return_width_binding_receipt_digest", "")),
        tuple(getattr(record, "call_site_return_width_receipt_digests", ()) or ()),
        tuple(
            tuple(item)
            for item in tuple(
                getattr(record, "call_site_return_width_receipt_assertion_digests", ())
                or ()
            )
        ),
        tuple(getattr(record, "canonical_return_width_receipt_digests", ()) or ()),
    ))


_PROJECTION_BINDING_START = re.compile(
    r"^; call_projection_binding ([0-9a-f]{64}) assertion_sha256=([0-9a-f]{64})$"
)
_PROJECTION_BINDING_END = re.compile(
    r"^; call_projection_binding_end ([0-9a-f]{64})$"
)
_CALL_SITE_WIDTH_MARKER = re.compile(
    r"^; call_site_return_width_receipt ([0-9a-f]{64}) "
    r"assertion_sha256=([0-9a-f]{64})$"
)


def _projection_evidence(formula: str) -> Optional[Mapping[str, str]]:
    lines = str(formula or "").splitlines()
    evidence: dict[str, str] = {}
    index = 0
    while index < len(lines):
        match = _PROJECTION_BINDING_START.fullmatch(lines[index])
        if match is None:
            index += 1
            continue
        binding_id, expected_digest = match.groups()
        if binding_id in evidence:
            return None
        end_index = index + 1
        end_match = None
        while end_index < len(lines):
            end_match = _PROJECTION_BINDING_END.fullmatch(lines[end_index])
            if end_match is not None:
                break
            if _PROJECTION_BINDING_START.fullmatch(lines[end_index]) is not None:
                return None
            end_index += 1
        if end_match is None or end_match.group(1) != binding_id:
            return None
        assertion_text = "\n".join(lines[index + 1:end_index])
        if (
            not assertion_text.strip()
            or hashlib.sha256(assertion_text.encode("utf-8")).hexdigest()
            != expected_digest
        ):
            return None
        evidence[binding_id] = expected_digest
        index = end_index + 1
    return evidence


def _call_width_evidence(formula: str) -> Optional[Mapping[str, str]]:
    lines = str(formula or "").splitlines()
    evidence: dict[str, str] = {}
    for index, line in enumerate(lines):
        match = _CALL_SITE_WIDTH_MARKER.fullmatch(line)
        if match is None:
            continue
        if index + 1 >= len(lines) or not lines[index + 1].startswith("(assert "):
            return None
        receipt_digest, expected_digest = match.groups()
        actual_digest = hashlib.sha256(lines[index + 1].encode("utf-8")).hexdigest()
        if actual_digest != expected_digest:
            return None
        if receipt_digest in evidence and evidence[receipt_digest] != actual_digest:
            return None
        evidence[receipt_digest] = actual_digest
    return evidence


def _verify_query_execution_record(
    record: Any,
    expected: RenderedRegionQuery,
    _projection_parser=_projection_evidence,
    _call_width_parser=_call_width_evidence,
    _sha256=hashlib.sha256,
) -> bool:
    if (
        type(record).__module__
        != "scripts.function_tracer_pcode.proof.call_effect.preflight"
        or type(record).__qualname__ != "QueryExecutionRecord"
    ):
        return False
    formula = str(getattr(record, "formula_text", ""))
    projection = _projection_parser(formula)
    call_width = _call_width_parser(formula)
    canonical_width = tuple(sorted(set(
        re.findall(
            r"^; canonical_return_width_binding_receipt ([0-9a-f]{64})$",
            formula,
            flags=re.MULTILINE,
        )
        + re.findall(
            r"^; binding-receipt ([0-9a-f]{64})$",
            formula,
            flags=re.MULTILINE,
        )
    )))
    view_digest = str(getattr(record, "return_width_observation_view_digest", ""))
    binding_digest = str(getattr(record, "return_width_binding_receipt_digest", ""))
    return bool(
        projection is not None
        and call_width is not None
        and getattr(record, "query_label", None)
        == (
            f"monolithic.region:{expected.contract.region_id}:"
            f"{expected.contract.query_kind}"
        )
        and getattr(record, "proof_kind", None)
        == (
            "monolithic_region_guard"
            if expected.contract.query_kind == "guard"
            else "monolithic_region_value_inequality"
        )
        and formula == expected.formula
        and _sha256(formula.encode("utf-8")).hexdigest()
        == expected.contract.formula_digest
        and getattr(record, "formula_digest", None) == expected.contract.formula_digest
        and getattr(record, "premise_digest", None) == expected.contract.contract_digest
        and tuple(sorted(projection))
        == tuple(sorted(getattr(record, "projection_binding_ids", ()) or ()))
        and getattr(record, "disposition", None) in {"unsat", "sat", "unknown", "error"}
        and (not view_digest or len(view_digest) == 64)
        and (not binding_digest or len(binding_digest) == 64)
        and bool(view_digest) == bool(binding_digest)
        and tuple(sorted(call_width)) == tuple(sorted(set(
            getattr(record, "call_site_return_width_receipt_digests", ()) or ()
        )))
        and tuple(sorted(call_width.items())) == tuple(sorted(set(
            tuple(item) for item in tuple(
                getattr(record, "call_site_return_width_receipt_assertion_digests", ())
                or ()
            )
        )))
        and canonical_width == tuple(sorted(set(
            getattr(record, "canonical_return_width_receipt_digests", ()) or ()
        )))
        and (not binding_digest or bool(canonical_width))
    )


def seal_monolithic_proof_bundle(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    query_set: ExpectedRegionQuerySet,
    execution_receipts: Sequence[RegionSolverExecutionReceipt],
    query_records: Sequence[Any],
    outcome_kind: str,
    session_certificate: SharedZ3SessionCertificate,
) -> MonolithicProofVerificationBundle:
    execution_receipts = tuple(execution_receipts)
    query_records = tuple(query_records)
    execution_digests = tuple(item.receipt_digest for item in execution_receipts)
    record_digests = tuple(_record_digest(item) for item in query_records)
    fields = (
        frozen.surface_digest,
        census.census_digest,
        query_set.query_set_digest,
        execution_digests,
        record_digests,
        outcome_kind,
    )
    bundle_digest = _digest(("monolithic_proof_verification_bundle_v1", *fields))
    payload = ("monolithic_proof_verification_bundle_v1", bundle_digest, *fields)
    return MonolithicProofVerificationBundle(
        bundle_digest,
        *fields,
        _seal(payload),
        frozen,
        census,
        query_set,
        execution_receipts,
        query_records,
        session_certificate,
    )


def verify_monolithic_proof_bundle(
    bundle: Any,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
    _verify_frozen=_verify_frozen_surface,
    _reconstruct_census=reconstruct_canonical_census,
    _build_query_set=build_expected_region_query_set,
    _verify_query_set=_verify_expected_query_set,
    _find_query=_query_from_set,
    _verify_session=_verify_session_certificate,
    _verify_execution=_verify_region_execution_receipt,
    _record_digest_fn=_record_digest,
    _verify_record=_verify_query_execution_record,
) -> bool:
    """Independently reconstruct ExpectedP and verify exact execution closure."""
    if type(bundle) is LegacyMonolithicCounterexampleProofBundle:
        fields = (
            bundle.frozen_surface_digest,
            bundle.census_digest,
            bundle.legacy_replay_receipt_digest,
            bundle.whole_surface_replay_receipt_digest,
            bundle.outcome_kind,
        )
        payload = (
            "legacy_monolithic_counterexample_proof_bundle_v1",
            bundle.bundle_digest,
            *fields,
        )
        legacy = bundle.legacy_replay_receipt
        whole = bundle.whole_surface_replay_receipt
        return bool(
            bundle.outcome_kind == "decisive_counterexample"
            and _compare(bundle.seal, _seal_fn(payload))
            and _verify_frozen(bundle.frozen)
            and bundle.census.census_digest
            == reconstruct_fallback_census(bundle.frozen).census_digest
            and bundle.frozen_surface_digest == bundle.frozen.surface_digest
            and bundle.census_digest == bundle.census.census_digest
            and type(legacy) is ReplayQueryExecutionReceipt
            and type(whole) is ReplayQueryExecutionReceipt
            and legacy.validates(bundle.frozen, bundle.census)
            and whole.validates(bundle.frozen, bundle.census)
            and legacy.contract.replay_kind == "legacy_violation_predicate"
            and whole.contract.replay_kind
            == "global_case_validation:whole_surface"
            and legacy.disposition == whole.disposition == "sat"
            and legacy.contract.model_digest == whole.contract.model_digest
            and legacy.contract.fixed_model_assertion_digest
            == whole.contract.fixed_model_assertion_digest
            and legacy.contract.formula_digest == whole.contract.formula_digest
            and bundle.legacy_replay_receipt_digest == legacy.receipt_digest
            and bundle.whole_surface_replay_receipt_digest == whole.receipt_digest
            and bundle.bundle_digest == _digest((
                "legacy_monolithic_counterexample_proof_bundle_v1", *fields
            ))
        )
    if type(bundle) is not MonolithicProofVerificationBundle:
        return False
    fields = (
        bundle.frozen_surface_digest,
        bundle.census_digest,
        bundle.query_set_digest,
        bundle.execution_receipt_digests,
        bundle.record_digests,
        bundle.outcome_kind,
    )
    payload = ("monolithic_proof_verification_bundle_v1", bundle.bundle_digest, *fields)
    if not _compare(bundle.seal, _seal_fn(payload)) or not _verify_frozen(bundle.frozen):
        return False
    reconstructed_census = _reconstruct_census(bundle.frozen)
    if reconstructed_census is None or reconstructed_census != bundle.census:
        return False
    reconstructed_queries = _build_query_set(
        bundle.frozen, reconstructed_census, bundle.query_set.base_ctx
    )
    if (
        not _verify_query_set(
            bundle.query_set, bundle.frozen, bundle.census
        )
        or reconstructed_queries.ordered_contract_digests
        != bundle.query_set.ordered_contract_digests
        or reconstructed_queries.query_set_digest != bundle.query_set.query_set_digest
        or tuple(item.receipt_digest for item in bundle.execution_receipts)
        != bundle.execution_receipt_digests
        or tuple(_record_digest_fn(item) for item in bundle.query_records)
        != bundle.record_digests
    ):
        return False
    executions: dict[Tuple[str, str], RegionSolverExecutionReceipt] = {}
    for execution in bundle.execution_receipts:
        key = (execution.region_id, execution.query_kind)
        if key in executions:
            return False
        try:
            expected = _find_query(reconstructed_queries, *key)
        except RuntimeError:
            return False
        if not _verify_session(
            bundle.session_certificate,
            reconstructed_queries,
            bundle.frozen,
            reconstructed_census,
        ) or not _verify_execution(
            execution, expected, bundle.session_certificate
        ):
            return False
        executions[key] = execution
    records: dict[Tuple[str, str], Any] = {}
    for record in bundle.query_records:
        label = str(getattr(record, "query_label", ""))
        match = re.fullmatch(r"monolithic\.region:([^:]+:[^:]+):(guard|value)", label)
        if match is None:
            # Replay records are verified by the counterexample authority lane.
            continue
        key = (match.group(1), match.group(2))
        if key in records or key not in executions:
            return False
        execution = executions[key]
        expected = _find_query(reconstructed_queries, *key)
        if not (
            _verify_record(record, expected)
            and getattr(record, "disposition", None) == execution.disposition
        ):
            return False
        records[key] = record
    closed = []
    sat_regions = []
    for region_id in reconstructed_census.expected_region_ids:
        guard = executions.get((region_id, "guard"))
        if guard is None or (region_id, "guard") not in records:
            return False
        if guard.disposition == "unsat":
            closed.append(region_id)
            if (region_id, "value") in executions or (region_id, "value") in records:
                return False
            continue
        if guard.disposition == "unknown":
            continue
        value = executions.get((region_id, "value"))
        if value is None or (region_id, "value") not in records:
            return False
        if value.disposition == "unsat":
            closed.append(region_id)
        elif value.disposition == "sat":
            sat_regions.append(region_id)
    if bundle.outcome_kind == "eq_closure":
        return tuple(closed) == reconstructed_census.expected_region_ids and not sat_regions
    if bundle.outcome_kind == "decisive_counterexample":
        return bool(sat_regions)
    return bundle.outcome_kind == "inconclusive_diagnostic"


@dataclass(frozen=True)
class ReplayQueryContract:
    contract_digest: str
    replay_kind: str
    frozen_surface_digest: str
    census_digest: str
    model_digest: str
    fixed_model_assertion_digest: str
    formula_digest: str
    seal: str

    def validates(self, frozen: FrozenSurface, census: CanonicalRegionCensus) -> bool:
        fields = (
            self.replay_kind,
            self.frozen_surface_digest,
            self.census_digest,
            self.model_digest,
            self.fixed_model_assertion_digest,
            self.formula_digest,
        )
        return bool(
            census.validates(frozen)
            and self.frozen_surface_digest == frozen.surface_digest
            and self.census_digest == census.census_digest
            and self.contract_digest == _digest(("replay_query_contract_v1", *fields))
            and hmac.compare_digest(
                self.seal,
                _seal(("replay_query_contract_v1", self.contract_digest, *fields)),
            )
        )


@dataclass(frozen=True)
class ReplayQueryExecutionReceipt:
    receipt_digest: str
    contract: ReplayQueryContract
    disposition: str
    solver_result_digest: str
    seal: str

    def validates(self, frozen: FrozenSurface, census: CanonicalRegionCensus) -> bool:
        fields = (
            self.contract.contract_digest,
            self.disposition,
            self.solver_result_digest,
        )
        return bool(
            self.contract.validates(frozen, census)
            and self.disposition in {"unsat", "sat", "unknown"}
            and self.receipt_digest == _digest(("replay_query_execution_receipt_v1", *fields))
            and hmac.compare_digest(
                self.seal,
                _seal(("replay_query_execution_receipt_v1", self.receipt_digest, *fields)),
            )
        )


def _verify_replay_contract(
    contract: ReplayQueryContract,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
) -> bool:
    if type(contract) is not ReplayQueryContract:
        return False
    fields = (
        contract.replay_kind,
        contract.frozen_surface_digest,
        contract.census_digest,
        contract.model_digest,
        contract.fixed_model_assertion_digest,
        contract.formula_digest,
    )
    return bool(
        _verify_canonical_census(census, frozen)
        and contract.frozen_surface_digest == frozen.surface_digest
        and contract.census_digest == census.census_digest
        and contract.contract_digest == _digest(("replay_query_contract_v1", *fields))
        and hmac.compare_digest(
            contract.seal,
            _seal(("replay_query_contract_v1", contract.contract_digest, *fields)),
        )
    )


def _verify_replay_receipt(
    receipt: ReplayQueryExecutionReceipt,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
) -> bool:
    if type(receipt) is not ReplayQueryExecutionReceipt:
        return False
    fields = (
        receipt.contract.contract_digest,
        receipt.disposition,
        receipt.solver_result_digest,
    )
    return bool(
        _verify_replay_contract(receipt.contract, frozen, census)
        and receipt.disposition in {"unsat", "sat", "unknown"}
        and receipt.receipt_digest
        == _digest(("replay_query_execution_receipt_v1", *fields))
        and hmac.compare_digest(
            receipt.seal,
            _seal(("replay_query_execution_receipt_v1", receipt.receipt_digest, *fields)),
        )
    )


def _make_replay_contract(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    *,
    replay_kind: str,
    model_digest: str,
    fixed_model_assertion_digest: str,
    formula: str,
) -> ReplayQueryContract:
    fields = (
        replay_kind,
        frozen.surface_digest,
        census.census_digest,
        model_digest,
        fixed_model_assertion_digest,
        hashlib.sha256(formula.encode("utf-8")).hexdigest(),
    )
    digest = _digest(("replay_query_contract_v1", *fields))
    return ReplayQueryContract(
        digest, *fields, _seal(("replay_query_contract_v1", digest, *fields))
    )


def _issue_replay_execution_receipt(
    contract: ReplayQueryContract,
    solver_result: Any,
) -> ReplayQueryExecutionReceipt:
    fields = (
        contract.contract_digest,
        _solver_disposition(solver_result),
        _solver_result_digest(solver_result),
    )
    digest = _digest(("replay_query_execution_receipt_v1", *fields))
    return ReplayQueryExecutionReceipt(
        digest,
        contract,
        fields[1],
        fields[2],
        _seal(("replay_query_execution_receipt_v1", digest, *fields)),
    )


def execute_legacy_violation_replay(
    strategy: Any,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    *,
    formula: str,
    model_digest: str,
    fixed_model_assertion_digest: str,
    timeout: int,
) -> Tuple[Any, ReplayQueryExecutionReceipt]:
    contract = _make_replay_contract(
        frozen,
        census,
        replay_kind="legacy_violation_predicate",
        model_digest=model_digest,
        fixed_model_assertion_digest=fixed_model_assertion_digest,
        formula=formula,
    )
    runner = (
        strategy.solver_runner.run_sequential
        if strategy.debug else strategy.solver_runner.run_parallel
    )
    result = runner(formula, timeout=timeout)
    return result, _issue_replay_execution_receipt(contract, result)


def execute_global_violation_replay(
    strategy: Any,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    *,
    formula: str,
    model_digest: str,
    fixed_model_assertion_digest: str,
    timeout: int,
) -> Tuple[Any, ReplayQueryExecutionReceipt]:
    """Execute an independent whole-surface replay under the fixed model."""
    contract = _make_replay_contract(
        frozen,
        census,
        replay_kind="global_case_validation:whole_surface",
        model_digest=model_digest,
        fixed_model_assertion_digest=fixed_model_assertion_digest,
        formula=formula,
    )
    runner = (
        strategy.solver_runner.run_sequential
        if strategy.debug else strategy.solver_runner.run_parallel
    )
    result = runner(formula, timeout=timeout)
    return result, _issue_replay_execution_receipt(contract, result)


def seal_legacy_counterexample_proof_bundle(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    legacy_replay_receipt: ReplayQueryExecutionReceipt,
    whole_surface_replay_receipt: ReplayQueryExecutionReceipt,
) -> LegacyMonolithicCounterexampleProofBundle:
    """Seal two independent SAT executions of the same fixed-model surface."""

    fields = (
        frozen.surface_digest,
        census.census_digest,
        legacy_replay_receipt.receipt_digest,
        whole_surface_replay_receipt.receipt_digest,
        "decisive_counterexample",
    )
    digest = _digest(("legacy_monolithic_counterexample_proof_bundle_v1", *fields))
    payload = ("legacy_monolithic_counterexample_proof_bundle_v1", digest, *fields)
    bundle = LegacyMonolithicCounterexampleProofBundle(
        digest,
        *fields,
        _seal(payload),
        frozen,
        census,
        legacy_replay_receipt,
        whole_surface_replay_receipt,
    )
    if not verify_monolithic_proof_bundle(bundle):
        raise RuntimeError("legacy_monolithic_counterexample_proof_bundle_invalid")
    return bundle


def create_global_replay_collector(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    *,
    model_digest: str,
    fixed_model_assertion_digest: str,
) -> Tuple[list[ReplayQueryExecutionReceipt], Any]:
    receipts: list[ReplayQueryExecutionReceipt] = []

    def collect(query: str, label: str, solver_result: Any) -> None:
        contract = _make_replay_contract(
            frozen,
            census,
            replay_kind=f"global_case_validation:{label}",
            model_digest=model_digest,
            fixed_model_assertion_digest=fixed_model_assertion_digest,
            formula=query,
        )
        receipts.append(_issue_replay_execution_receipt(contract, solver_result))

    return receipts, collect


@dataclass(frozen=True)
class GateArtifactReference:
    reference_digest: str
    gate_kind: str
    artifact_id: str
    status: str
    not_required_reason: str
    frozen_surface_digest: str
    seal: str
    source_artifact: Any = field(repr=False, compare=False)

    def validates(self, frozen: FrozenSurface, census: CanonicalRegionCensus) -> bool:
        fields = (
            self.gate_kind,
            self.artifact_id,
            self.status,
            self.not_required_reason,
            self.frozen_surface_digest,
        )
        derived_status, derived_reason = _verify_gate_source(
            self.gate_kind, self.source_artifact, frozen, census
        )
        return bool(
            self.gate_kind in {"coverage", "effect", "projection", "width"}
            and self.status in {"proven", "not_required"}
            and self.frozen_surface_digest == frozen.surface_digest
            and self.status == derived_status
            and self.not_required_reason == derived_reason
            and (self.status != "not_required" or bool(self.not_required_reason))
            and self.artifact_id == gate_source_artifact_id(
                self.gate_kind, self.source_artifact
            )
            and self.reference_digest == _digest(("gate_artifact_reference_v1", *fields))
            and hmac.compare_digest(
                self.seal,
                _seal(("gate_artifact_reference_v1", self.reference_digest, *fields)),
            )
        )


def gate_source_artifact_id(gate_kind: str, source_artifact: Any) -> str:
    if gate_kind == "projection":
        return str(getattr(source_artifact, "projection_id", ""))
    if gate_kind == "coverage":
        coverage_ids = source_artifact[1] if isinstance(source_artifact, tuple) else ()
        payload = ("coverage", coverage_ids)
    elif gate_kind == "effect":
        manifest = source_artifact[0] if isinstance(source_artifact, tuple) else None
        artifacts = source_artifact[1] if isinstance(source_artifact, tuple) else ()
        payload = (
            "effect",
            dict(manifest or {}).get("structural_coverage_certificate", {}).get(
                "certificate_id", ""
            ),
            dict(manifest or {}).get("coupling", {}).get("coupling_id", ""),
            tuple(
                str(getattr(item, "artifact_id", getattr(item, "proof_id", repr(item))))
                for item in tuple(artifacts or ())
            ),
        )
    elif gate_kind == "width":
        if callable(getattr(source_artifact, "validate", None)):
            payload = ("width_bundle", getattr(source_artifact, "bundle_digest", ""))
        else:
            payload = (
                "equal_width",
                tuple(source_artifact[0].outcome_function_identity()),
                tuple(source_artifact[1].outcome_function_identity()),
            ) if isinstance(source_artifact, tuple) and len(source_artifact) == 2 else ()
    else:
        return ""
    return hashlib.sha256(repr(payload).encode("utf-8")).hexdigest()


def _single_unconditional_surface(cases: Sequence[Any]) -> bool:
    return bool(
        len(tuple(cases)) == 1
        and not tuple(getattr(tuple(cases)[0], "conditions", ()) or ())
    )


def _surface_value_widths(cases: Sequence[Any]) -> Tuple[int, ...]:
    widths = []
    for case in tuple(cases):
        value = getattr(case, "value_expr", None)
        try:
            width = int(getattr(value, "size", 0) or 0) * 8
        except (TypeError, ValueError):
            width = 0
        if width <= 0:
            return ()
        widths.append(width)
    return tuple(widths)


def _verify_gate_source(
    gate_kind: str,
    source_artifact: Any,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
) -> Tuple[str, str]:
    if not _verify_canonical_census(census, frozen):
        return "invalid", ""
    if gate_kind == "coverage":
        if not isinstance(source_artifact, tuple) or len(source_artifact) != 4:
            return "invalid", ""
        runtime, claimed_ids, analysis1, analysis2 = source_artifact
        from scripts.function_tracer_pcode.proof.return_width.pipeline import (
            return_coverage_artifact_ids,
        )
        actual_ids = return_coverage_artifact_ids(
            runtime,
            (tuple(analysis1.outcome_function_identity()),
             tuple(analysis2.outcome_function_identity())),
        )
        if tuple(claimed_ids) and tuple(claimed_ids) == tuple(actual_ids):
            return "proven", ""
        if (
            not tuple(claimed_ids)
            and not tuple(actual_ids)
            and _single_unconditional_surface(census.cases1)
            and _single_unconditional_surface(census.cases2)
        ):
            return "not_required", "single_unconditional_return_on_both_surfaces"
        return "invalid", ""
    if gate_kind == "projection":
        projection = source_artifact
        if (
            getattr(projection, "prepared_surface_digest", "")
            != frozen.prepared_surface_digest
            or int(getattr(projection, "generation", -1)) != frozen.generation
            or tuple(getattr(projection, "root_blockers", ()) or ())
        ):
            return "invalid", ""
        if getattr(projection, "required", True) is False:
            clean = not any((
                tuple(getattr(projection, "covered_blockers", ()) or ()),
                tuple(getattr(projection, "completed_obligation_ids", ()) or ()),
                tuple(getattr(projection, "semantic_bindings", ()) or ()),
            ))
            return (
                ("not_required", "no_observation_reachable_deferred_calls")
                if getattr(projection, "status", "") == "not_required" and clean
                else ("invalid", "")
            )
        bindings = tuple(getattr(projection, "semantic_bindings", ()) or ())
        completed = set(getattr(projection, "completed_obligation_ids", ()) or ())
        valid = bool(
            getattr(projection, "status", "") == "proven"
            and completed
            and bindings
            and all(
                getattr(item, "obligation_id", "") in completed
                and getattr(item, "binding_id", "")
                for item in bindings
            )
        )
        return ("proven", "") if valid else ("invalid", "")
    if gate_kind == "effect":
        if not isinstance(source_artifact, tuple) or len(source_artifact) != 3:
            return "invalid", ""
        manifest, artifacts, projection = source_artifact
        from scripts.function_tracer_pcode.proof.call_effect.obligations import (
            build_structural_coverage_certificate,
        )
        rebuilt = build_structural_coverage_certificate(manifest)
        persisted = dict(manifest or {}).get("structural_coverage_certificate", {})
        if getattr(projection, "required", True) is False:
            summary = dict(manifest or {}).get("summary", {}) or {}
            no_effects = not any(int(summary.get(key, 0) or 0) for key in (
                "left_fact_count", "right_fact_count", "obligation_count",
            ))
            return (
                ("not_required", "no_call_return_or_effect_obligations")
                if no_effects and getattr(projection, "status", "") == "not_required"
                else ("invalid", "")
            )
        artifact_valid = all(
            callable(getattr(item, "verification_failure", None))
            and item.verification_failure() is None
            for item in tuple(artifacts or ())
        )
        valid = bool(
            rebuilt.verification_failure() is None
            and persisted.get("certificate_id") == rebuilt.certificate_id
            and persisted.get("status") == "complete"
            and persisted.get("verification_status") == "verified"
            and artifact_valid
            and getattr(projection, "status", "") == "proven"
        )
        return ("proven", "") if valid else ("invalid", "")
    if gate_kind == "width":
        validate = getattr(source_artifact, "validate", None)
        if callable(validate):
            return ("proven", "") if validate() else ("invalid", "")
        if isinstance(source_artifact, tuple) and len(source_artifact) == 2:
            try:
                identities_match = (
                    tuple(source_artifact[0].outcome_function_identity())
                    == frozen.left_identity
                    and tuple(source_artifact[1].outcome_function_identity())
                    == frozen.right_identity
                )
            except (AttributeError, TypeError):
                identities_match = False
            left_widths = _surface_value_widths(census.cases1)
            right_widths = _surface_value_widths(census.cases2)
            if (
                identities_match
                and
                left_widths
                and right_widths
                and len(set((*left_widths, *right_widths))) == 1
            ):
                return "not_required", "equal_observed_return_width"
        return "invalid", ""
    return "invalid", ""


def _validate_gate_reference(
    reference: GateArtifactReference,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    _source_verifier=_verify_gate_source,
) -> bool:
    if type(reference) is not GateArtifactReference:
        return False
    fields = (
        reference.gate_kind,
        reference.artifact_id,
        reference.status,
        reference.not_required_reason,
        reference.frozen_surface_digest,
    )
    derived_status, derived_reason = _source_verifier(
        reference.gate_kind, reference.source_artifact, frozen, census
    )
    return bool(
        reference.gate_kind in {"coverage", "effect", "projection", "width"}
        and reference.status in {"proven", "not_required"}
        and reference.frozen_surface_digest == frozen.surface_digest
        and reference.status == derived_status
        and reference.not_required_reason == derived_reason
        and (reference.status != "not_required" or bool(reference.not_required_reason))
        and reference.artifact_id == gate_source_artifact_id(
            reference.gate_kind, reference.source_artifact
        )
        and reference.reference_digest == _digest(
            ("gate_artifact_reference_v1", *fields)
        )
        and hmac.compare_digest(
            reference.seal,
            _seal(("gate_artifact_reference_v1", reference.reference_digest, *fields)),
        )
    )


def issue_gate_artifact_reference(
    frozen: FrozenSurface,
    gate_kind: str,
    source_artifact: Any,
    *,
    artifact_id: str,
    status: str,
    census: Optional[CanonicalRegionCensus] = None,
) -> GateArtifactReference:
    if str(artifact_id) != gate_source_artifact_id(gate_kind, source_artifact):
        raise RuntimeError("gate_artifact_reference_source_mismatch")
    census = census or reconstruct_canonical_census(frozen)
    if census is None:
        raise RuntimeError("gate_artifact_reference_census_missing")
    derived_status, reason = _verify_gate_source(
        gate_kind, source_artifact, frozen, census
    )
    if status != derived_status or status not in {"proven", "not_required"}:
        raise RuntimeError("gate_artifact_reference_proof_invalid")
    fields = (gate_kind, str(artifact_id), status, reason, frozen.surface_digest)
    digest = _digest(("gate_artifact_reference_v1", *fields))
    return GateArtifactReference(
        digest,
        *fields,
        _seal(("gate_artifact_reference_v1", digest, *fields)),
        source_artifact,
    )


@dataclass(frozen=True)
class CounterexampleSafetyDecisionReceipt:
    receipt_digest: str
    frozen_surface_digest: str
    census_digest: str
    model_digest: str
    fixed_model_assertion_digest: str
    legacy_replay_receipt_digest: str
    global_replay_receipt_digests: Tuple[str, ...]
    gate_reference_digests: Tuple[str, ...]
    decision: str
    seal: str
    legacy_replay_receipt: ReplayQueryExecutionReceipt = field(repr=False, compare=False)
    global_replay_receipts: Tuple[ReplayQueryExecutionReceipt, ...] = field(repr=False, compare=False)
    gate_references: Tuple[GateArtifactReference, ...] = field(repr=False, compare=False)

    def validates(
        self,
        frozen: FrozenSurface,
        census: CanonicalRegionCensus,
        _gate_verifier=_validate_gate_reference,
    ) -> bool:
        fields = (
            self.frozen_surface_digest,
            self.census_digest,
            self.model_digest,
            self.fixed_model_assertion_digest,
            self.legacy_replay_receipt_digest,
            self.global_replay_receipt_digests,
            self.gate_reference_digests,
            self.decision,
        )
        gate_kinds = {item.gate_kind for item in self.gate_references}
        replays = (self.legacy_replay_receipt, *self.global_replay_receipts)
        whole_surface_replays = tuple(
            item for item in self.global_replay_receipts
            if item.contract.replay_kind == "global_case_validation:whole_surface"
        )
        return bool(
            census.validates(frozen)
            and self.frozen_surface_digest == frozen.surface_digest
            and self.census_digest == census.census_digest
            and self.decision == "safe_decisive"
            and self.legacy_replay_receipt.contract.replay_kind
            == "legacy_violation_predicate"
            and self.legacy_replay_receipt.disposition == "sat"
            and bool(self.global_replay_receipts)
            and all(item.validates(frozen, census) for item in replays)
            and all(item.disposition != "unknown" for item in replays)
            and len(whole_surface_replays) == 1
            and whole_surface_replays[0].disposition == "sat"
            and all(
                item.contract.model_digest == self.model_digest
                and item.contract.fixed_model_assertion_digest
                == self.fixed_model_assertion_digest
                for item in replays
            )
            and gate_kinds == {"coverage", "effect", "projection", "width"}
            and all(
                _gate_verifier(item, frozen, census)
                for item in self.gate_references
            )
            and self.legacy_replay_receipt.receipt_digest
            == self.legacy_replay_receipt_digest
            and tuple(item.receipt_digest for item in self.global_replay_receipts)
            == self.global_replay_receipt_digests
            and tuple(item.reference_digest for item in self.gate_references)
            == self.gate_reference_digests
            and self.receipt_digest == _digest(("counterexample_safety_decision_receipt_v1", *fields))
            and hmac.compare_digest(
                self.seal,
                _seal(("counterexample_safety_decision_receipt_v1", self.receipt_digest, *fields)),
            )
        )


def _verify_counterexample_safety_receipt(
    receipt: CounterexampleSafetyDecisionReceipt,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    _gate_verifier=_validate_gate_reference,
) -> bool:
    if type(receipt) is not CounterexampleSafetyDecisionReceipt:
        return False
    fields = (
        receipt.frozen_surface_digest,
        receipt.census_digest,
        receipt.model_digest,
        receipt.fixed_model_assertion_digest,
        receipt.legacy_replay_receipt_digest,
        receipt.global_replay_receipt_digests,
        receipt.gate_reference_digests,
        receipt.decision,
    )
    gate_kinds = {item.gate_kind for item in receipt.gate_references}
    replays = (receipt.legacy_replay_receipt, *receipt.global_replay_receipts)
    whole_surface_replays = tuple(
        item for item in receipt.global_replay_receipts
        if item.contract.replay_kind == "global_case_validation:whole_surface"
    )
    return bool(
        _verify_canonical_census(census, frozen)
        and receipt.frozen_surface_digest == frozen.surface_digest
        and receipt.census_digest == census.census_digest
        and receipt.decision == "safe_decisive"
        and receipt.legacy_replay_receipt.contract.replay_kind
        == "legacy_violation_predicate"
        and receipt.legacy_replay_receipt.disposition == "sat"
        and bool(receipt.global_replay_receipts)
        and all(_verify_replay_receipt(item, frozen, census) for item in replays)
        and all(item.disposition != "unknown" for item in replays)
        and len(whole_surface_replays) == 1
        and whole_surface_replays[0].disposition == "sat"
        and all(
            item.contract.model_digest == receipt.model_digest
            and item.contract.fixed_model_assertion_digest
            == receipt.fixed_model_assertion_digest
            for item in replays
        )
        and gate_kinds == {"coverage", "effect", "projection", "width"}
        and all(
            _gate_verifier(item, frozen, census)
            for item in receipt.gate_references
        )
        and receipt.legacy_replay_receipt.receipt_digest
        == receipt.legacy_replay_receipt_digest
        and tuple(item.receipt_digest for item in receipt.global_replay_receipts)
        == receipt.global_replay_receipt_digests
        and tuple(item.reference_digest for item in receipt.gate_references)
        == receipt.gate_reference_digests
        and receipt.receipt_digest
        == _digest(("counterexample_safety_decision_receipt_v1", *fields))
        and hmac.compare_digest(
            receipt.seal,
            _seal((
                "counterexample_safety_decision_receipt_v1",
                receipt.receipt_digest,
                *fields,
            )),
        )
    )


_PINNED_COUNTEREXAMPLE_SAFETY_VERIFIER = _verify_counterexample_safety_receipt


def issue_counterexample_safety_decision_receipt(
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    *,
    model_digest: str,
    fixed_model_assertion_digest: str,
    legacy_replay_receipt: ReplayQueryExecutionReceipt,
    global_replay_receipts: Sequence[ReplayQueryExecutionReceipt],
    gate_references: Sequence[GateArtifactReference],
) -> CounterexampleSafetyDecisionReceipt:
    global_replay_receipts = tuple(global_replay_receipts)
    gate_references = tuple(gate_references)
    fields = (
        frozen.surface_digest,
        census.census_digest,
        model_digest,
        fixed_model_assertion_digest,
        legacy_replay_receipt.receipt_digest,
        tuple(item.receipt_digest for item in global_replay_receipts),
        tuple(item.reference_digest for item in gate_references),
        "safe_decisive",
    )
    digest = _digest(("counterexample_safety_decision_receipt_v1", *fields))
    receipt = CounterexampleSafetyDecisionReceipt(
        digest,
        *fields,
        _seal(("counterexample_safety_decision_receipt_v1", digest, *fields)),
        legacy_replay_receipt,
        global_replay_receipts,
        gate_references,
    )
    if not _PINNED_COUNTEREXAMPLE_SAFETY_VERIFIER(receipt, frozen, census):
        raise RuntimeError("counterexample_safety_decision_receipt_invalid")
    return receipt


def reconstruct_fallback_census(frozen: FrozenSurface) -> CanonicalRegionCensus:
    """Bind a legacy relation/width query to an explicit one-region census."""
    expected = ("legacy",)
    cases1 = tuple(_pinned_extract_cases(
        frozen.analysis1,
        frozen.normalization_settings,
        apply_effective_partition=False,
    ))
    cases2 = tuple(_pinned_extract_cases(
        frozen.analysis2,
        frozen.normalization_settings,
        apply_effective_partition=False,
    ))
    left_ids = tuple(_case_identity(case) for case in cases1) or (
        ("legacy_surface", frozen.left_identity),
    )
    right_ids = tuple(_case_identity(case) for case in cases2) or (
        ("legacy_surface", frozen.right_identity),
    )
    census_digest = _digest(("canonical_monolithic_census_v1", frozen.surface_digest,
                             left_ids, right_ids, expected))
    payload = ("canonical_monolithic_census_v1", census_digest, frozen.surface_digest,
               expected, left_ids, right_ids)
    return CanonicalRegionCensus(census_digest, frozen.surface_digest, expected,
                                 left_ids, right_ids, _seal(payload), cases1, cases2)


@dataclass(frozen=True)
class MonolithicTerminalDecisionReceipt:
    receipt_digest: str
    outcome_kind: str
    comparison_receipt_id: str
    parent_lease_digest: str
    execution_lease_digest: str
    frozen_surface_digest: str
    census_digest: str
    region_receipt_digests: Tuple[str, ...]
    sat_region_id: str
    model_digest: str
    fixed_model_assertion_digest: str
    legacy_replay_receipt_digest: str
    counterexample_safety_receipt_digest: str
    proof_bundle_digest: str
    gate_reference_digests: Tuple[str, ...]
    diagnostic_reason_digests: Tuple[str, ...]
    seal: str
    proof_bundle: Any = field(default=None, repr=False, compare=False)
    counterexample_safety_receipt: Any = field(default=None, repr=False, compare=False)
    frozen_surface: Any = field(default=None, repr=False, compare=False)
    canonical_census: Any = field(default=None, repr=False, compare=False)

    def validates(self) -> bool:
        return verify_terminal_decision_receipt(self)


def verify_terminal_decision_receipt(
    receipt: MonolithicTerminalDecisionReceipt,
    _safety_verifier=_PINNED_COUNTEREXAMPLE_SAFETY_VERIFIER,
    _proof_verifier=verify_monolithic_proof_bundle,
    _seal_fn=_seal,
    _compare=hmac.compare_digest,
) -> bool:
    if type(receipt) is not MonolithicTerminalDecisionReceipt:
        return False
    self = receipt
    payload = ("monolithic_terminal_decision_receipt_v1", self.receipt_digest,
                   self.outcome_kind, self.comparison_receipt_id,
                   self.parent_lease_digest, self.execution_lease_digest,
                   self.frozen_surface_digest, self.census_digest,
                   self.region_receipt_digests, self.sat_region_id,
                   self.model_digest, self.fixed_model_assertion_digest,
                   self.legacy_replay_receipt_digest,
                   self.counterexample_safety_receipt_digest,
                   self.proof_bundle_digest,
                   self.gate_reference_digests, self.diagnostic_reason_digests)
    if not _compare(self.seal, _seal_fn(payload)):
        return False
    if self.outcome_kind == "eq_closure":
        return bool(
            self.region_receipt_digests
            and self.gate_reference_digests
            and (
                self.proof_bundle_digest == "explicit_legacy_validation_control"
                and self.proof_bundle is None
                or self.proof_bundle is not None
                and self.proof_bundle_digest == self.proof_bundle.bundle_digest
                and _proof_verifier(self.proof_bundle)
                and self.proof_bundle.outcome_kind == "eq_closure"
            )
        )
    if self.outcome_kind == "decisive_counterexample":
        safety = self.counterexample_safety_receipt
        return bool(
            all((self.sat_region_id, self.model_digest,
                 self.fixed_model_assertion_digest,
                 self.legacy_replay_receipt_digest,
                 self.counterexample_safety_receipt_digest,
                 self.proof_bundle_digest, self.gate_reference_digests))
            and self.proof_bundle is not None
            and self.proof_bundle_digest == self.proof_bundle.bundle_digest
            and _proof_verifier(self.proof_bundle)
            and self.proof_bundle.outcome_kind == "decisive_counterexample"
            and safety is not None
            and self.frozen_surface is not None
            and self.canonical_census is not None
            and safety.receipt_digest == self.counterexample_safety_receipt_digest
            and safety.model_digest == self.model_digest
            and safety.fixed_model_assertion_digest == self.fixed_model_assertion_digest
            and safety.legacy_replay_receipt_digest == self.legacy_replay_receipt_digest
            and safety.gate_reference_digests == self.gate_reference_digests
            and _safety_verifier(
                safety, self.frozen_surface, self.canonical_census
            )
        )
    return self.outcome_kind == "inconclusive_diagnostic" and bool(self.diagnostic_reason_digests)


def seal_terminal_decision(
    parent: ProductionBranchAuthorityLease,
    execution: MonolithicExecutionAuthorityLease,
    frozen: FrozenSurface,
    census: CanonicalRegionCensus,
    *,
    outcome_kind: str,
    comparison_receipt_id: str,
    region_receipt_digests: Sequence[str],
    sat_region_id: str = "",
    model_digest: str = "",
    fixed_model_assertion_digest: str = "",
    legacy_replay_receipt_digest: str = "",
    counterexample_safety_receipt_digest: str = "",
    proof_bundle: Any = None,
    counterexample_safety_receipt: Any = None,
    explicit_legacy_validation_control: bool = False,
    gate_reference_digests: Sequence[str] = (),
    diagnostic_reason_digests: Sequence[str] = (),
) -> MonolithicTerminalDecisionReceipt:
    if not _verify_execution_lease(execution, parent) or not _verify_canonical_census(census, frozen):
        raise RuntimeError("monolithic_terminal_authority_inactive")
    proof_bundle_digest = (
        str(getattr(proof_bundle, "bundle_digest", ""))
        if proof_bundle is not None else
        "explicit_legacy_validation_control"
        if explicit_legacy_validation_control else ""
    )
    if outcome_kind in {"eq_closure", "decisive_counterexample"}:
        legacy_eq = bool(
            outcome_kind == "eq_closure"
            and explicit_legacy_validation_control
            and proof_bundle is None
        )
        if not legacy_eq and (
            proof_bundle is None or not verify_monolithic_proof_bundle(proof_bundle)
        ):
            raise RuntimeError("monolithic_terminal_proof_bundle_invalid")
    if outcome_kind == "decisive_counterexample":
        if (
            counterexample_safety_receipt is None
            or not _verify_counterexample_safety_receipt(
                counterexample_safety_receipt, frozen, census
            )
            or counterexample_safety_receipt.receipt_digest
            != counterexample_safety_receipt_digest
        ):
            raise RuntimeError("monolithic_counterexample_safety_receipt_invalid")
    fields = (outcome_kind, comparison_receipt_id, parent.digest, execution.digest,
              frozen.surface_digest, census.census_digest, tuple(region_receipt_digests),
              sat_region_id, model_digest, fixed_model_assertion_digest,
              legacy_replay_receipt_digest, counterexample_safety_receipt_digest,
              proof_bundle_digest,
              tuple(gate_reference_digests), tuple(diagnostic_reason_digests))
    receipt_digest = _digest(("monolithic_terminal_decision_receipt_v1", *fields))
    payload = ("monolithic_terminal_decision_receipt_v1", receipt_digest, *fields)
    receipt = MonolithicTerminalDecisionReceipt(
        receipt_digest, *fields, _seal(payload), proof_bundle,
        counterexample_safety_receipt, frozen, census,
    )
    if not verify_terminal_decision_receipt(receipt):
        raise RuntimeError("monolithic_terminal_receipt_incomplete")
    return receipt
