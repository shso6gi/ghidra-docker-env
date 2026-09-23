"""Region plans, execution contexts and case identities shared by the monolithic strategy and its mixins."""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field, replace
from typing import Optional, Dict, Any, Mapping, Tuple
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.structural import condition_key, expression_provenance_key
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    InputCorrespondenceSet,
)
from scripts.function_tracer_pcode.proof.monolithic_authority import (
    build_expected_region_query_set as _PINNED_BUILD_EXPECTED_REGION_QUERY_SET,
    create_shared_z3_region_session as _PINNED_CREATE_SHARED_Z3_REGION_SESSION,
    execute_expected_guard_query as _PINNED_EXECUTE_EXPECTED_GUARD_QUERY,
    execute_expected_value_query as _PINNED_EXECUTE_EXPECTED_VALUE_QUERY,
)


@dataclass(frozen=True)
class _MonolithicReturnWidthQueryBundle:
    canonical_width: int
    observations_by_pair: Tuple[Tuple[str, Any], ...]
    left_case_identities: Tuple[Tuple[Any, ...], ...]
    right_case_identities: Tuple[Tuple[Any, ...], ...]
    ordered_receipt_digests: Tuple[str, ...]
    ordered_markers: Tuple[str, ...]
    view_digest: str
    binding_digest: str
    production_query_digest: str = ""
    production_query_text: str = field(default="", repr=False, compare=False)

    @property
    def bundle_digest(self) -> str:
        return hashlib.sha256(repr((
            "monolithic_return_width_query_bundle_v1",
            self.canonical_width,
            tuple(pair_id for pair_id, _ in self.observations_by_pair),
            self.left_case_identities,
            self.right_case_identities,
            self.ordered_receipt_digests,
            self.ordered_markers,
            self.view_digest,
            self.binding_digest,
            self.production_query_digest,
        )).encode("utf-8")).hexdigest()

    def bind_query(self, query: str) -> "_MonolithicReturnWidthQueryBundle":
        query_digest = hashlib.sha256(query.encode("utf-8")).hexdigest()
        markers = tuple(re.findall(
            r"^; canonical_return_width_binding_receipt [0-9a-f]{64}$",
            query,
            flags=re.MULTILINE,
        ))
        if markers != self.ordered_markers:
            raise ValueError("monolithic_canonical_binding_receipt_order_mismatch")
        return replace(
            self,
            production_query_digest=query_digest,
            production_query_text=query,
        )

    def validate(self) -> bool:
        return bool(
            self.production_query_text
            and len(self.production_query_digest) == 64
            and hashlib.sha256(
                self.production_query_text.encode("utf-8")
            ).hexdigest() == self.production_query_digest
            and tuple(re.findall(
                r"^; canonical_return_width_binding_receipt [0-9a-f]{64}$",
                self.production_query_text,
                flags=re.MULTILINE,
            )) == self.ordered_markers
            and tuple(
                observation.binding_receipt.binding_digest
                for _, observation in self.observations_by_pair
            ) == self.ordered_receipt_digests
        )


def _monolithic_case_identity(case: Any) -> Tuple[Any, ...]:
    return (
        "monolithic_return_case_v1",
        int(getattr(case, "index", -1)),
        tuple(int(item) for item in tuple(getattr(case, "source_indices", ()) or ())),
        tuple(expression_provenance_key(getattr(case, "value_expr", None))),
        tuple(condition_key(item) for item in tuple(getattr(case, "conditions", ()) or ())),
    )


@dataclass(frozen=True)
class _MonolithicDecisionExecutionContext:
    decision_surface: str
    analysis_object_ids: tuple[int, int]
    prepared_surface_digest: Optional[str] = None
    return_width_query_bundle: Optional[_MonolithicReturnWidthQueryBundle] = None

    @classmethod
    def create(
        cls,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        decision_surface: str,
        prepared_surface_digest: Optional[str] = None,
    ) -> "_MonolithicDecisionExecutionContext":
        if decision_surface not in {"prepared", "legacy_source"}:
            raise ValueError("invalid_monolithic_decision_surface")
        if decision_surface == "prepared" and not prepared_surface_digest:
            raise ValueError("prepared_monolithic_surface_digest_missing")
        if decision_surface == "legacy_source" and prepared_surface_digest is not None:
            raise ValueError("legacy_monolithic_surface_has_prepared_digest")
        return cls(
            decision_surface=decision_surface,
            analysis_object_ids=(id(analysis1), id(analysis2)),
            prepared_surface_digest=prepared_surface_digest,
        )

    def assert_bound_to(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> None:
        if self.analysis_object_ids != (id(analysis1), id(analysis2)):
            raise RuntimeError("monolithic_decision_context_analysis_mismatch")

    @property
    def uses_prepared_surface(self) -> bool:
        return self.decision_surface == "prepared"

    def with_return_width_query_bundle(
        self,
        bundle: _MonolithicReturnWidthQueryBundle,
    ) -> "_MonolithicDecisionExecutionContext":
        if not bundle.validate():
            raise ValueError("monolithic_return_width_query_bundle_invalid")
        return replace(self, return_width_query_bundle=bundle)


@dataclass(frozen=True)
class _MonolithicRegionPlan:
    plan_digest: str
    expected_region_ids: Tuple[str, ...]
    cases1: Tuple[Any, ...] = field(repr=False, compare=False)
    cases2: Tuple[Any, ...] = field(repr=False, compare=False)
    frozen_surface: Any = field(default=None, repr=False, compare=False)
    census: Any = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class _MonolithicRegionExecution:
    final_is_equivalent: Optional[bool]
    parallel_result: ParallelResult
    counterexample_raw: Optional[Dict[str, Any]]
    last_formula: str
    query_records: Tuple[Any, ...]
    disposition_counts: Mapping[str, int]
    debug_stats: Mapping[str, int]
    plan: _MonolithicRegionPlan
    sat_region_id: str = ""
    model_digest: str = ""
    fixed_model_assertion_digest: str = ""
    legacy_replay_receipt_digest: str = ""
    legacy_replay_receipt: Any = None
    execution_receipts: Tuple[Any, ...] = ()
    expected_query_set: Any = None
    session_certificate: Any = None
    sat_replay_formula: str = field(default="", repr=False, compare=False)
    sat_replay_census: Any = field(default=None, repr=False, compare=False)


def active_input_correspondence(strategy: Any) -> Optional[InputCorrespondenceSet]:
    """実行中の ``check()`` が使う最終 InputCorrespondence（Issue #167）。

    ``MonolithicStrategy.check`` が冒頭で dispatch frame（無ければ raw pair）から
    1 回だけ決めて ``_active_input_correspondence`` に置く。mixin はここからだけ
    読み、builder と normalizer へ同じ値を渡す。未設定なら None（builder は渡された
    raw analysis から作る）。
    """

    correspondence = getattr(strategy, "_active_input_correspondence", None)
    return correspondence if type(correspondence) is InputCorrespondenceSet else None


def active_input_authorization(strategy: Any, side: str):
    correspondence = active_input_correspondence(strategy)
    return None if correspondence is None else correspondence.authorization(side)

