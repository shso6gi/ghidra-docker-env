"""Read-only reduction proofs, references and lowerings."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.json_encoding import (as_list, each, inline, is_json_record, mapping_of, materialize, nested, raw, source_converter)
from scripts.function_tracer_pcode.core.runtime_refs.locations import (
    LocationBaseRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.loops import (
    LoopSideEffectProfileRef,
    LoopSummaryRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PcodeBlockRef,
    PcodeOpRef,
)


@dataclass(frozen=True)
class ReadonlyReductionTermRef:
    """Object-centric description of one scalar term in a memory reduction."""

    byte_offset: int
    access_size: int

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "readonly_reduction_term",
            int(self.byte_offset),
            max(1, int(self.access_size or 0)),
        )

    def json_items(self):
        yield "kind", "readonly_reduction_term"
        yield "byte_offset", int(self.byte_offset)
        yield "access_size", max(1, int(self.access_size or 0))

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReadonlyReductionWitness:
    """Concrete count-parameter witness for a readonly reduction."""

    exact_count: int
    terms: Tuple[ReadonlyReductionTermRef, ...]
    count_semantics: str = "count_parameter"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "readonly_reduction_witness",
            self.count_semantics,
            int(self.exact_count),
            tuple(term.stable_key() for term in self.terms),
        )

    def json_items(self):
        yield "kind", "readonly_reduction_witness"
        yield "count_semantics", self.count_semantics
        yield "exact_count", int(self.exact_count)
        yield "terms", each(self.terms)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReductionAccumulatorProof:
    """Object-centric proof that a loop accumulator is a readonly reduction.

    This is intentionally richer than the runtime summaries it can lower to.
    Runtime refs describe what can be compared today; this proof records the
    Ghidra/SMT-relevant evidence used to justify that lowering, including PHI
    roles, CFG anchors, seed terms, lane terms, exact return witnesses, and
    constant bias.  Consumers should preserve this object when future lowerings
    need more detail than ``READONLY_SUM(base, count)`` can currently express.
    """

    reduction_kind: str
    pointer_base_ref: LocationBaseRef
    count_parameter_name: str
    count_parameter_index: Optional[int]
    limit_expr: Any
    result_size: int
    stride: int
    element_size: int
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]] = None
    start_offset: int = 0
    start_index: int = 0
    index_step: int = 1
    index_scale: int = 0
    signed_counter: bool = True
    seed_terms: Tuple[ReadonlyReductionTermRef, ...] = ()
    seed_term_count: Optional[int] = None
    lane_terms: Tuple[Tuple[int, int], ...] = ()
    loop_body_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()
    exact_return_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()
    guard_constraints: Tuple[Any, ...] = ()
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef(
        profile="pure_memory_read",
        memory_reads=True,
    )
    constant_bias: int = 0
    induction_phi_ref: Optional[PcodeOpRef] = None
    accumulator_phi_ref: Optional[PcodeOpRef] = None
    update_op_ref: Optional[PcodeOpRef] = None
    load_op_refs: Tuple[PcodeOpRef, ...] = ()
    return_op_refs: Tuple[PcodeOpRef, ...] = ()
    return_value_op_refs: Tuple[PcodeOpRef, ...] = ()
    entry_block_ref: Optional[PcodeBlockRef] = None
    backedge_block_ref: Optional[PcodeBlockRef] = None
    return_region_value_proven: bool = False
    source: str = "recurrence_summary"

    def __post_init__(self) -> None:
        if int(self.stride) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive stride")
        if int(self.element_size) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive element_size")
        if int(self.result_size) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive result_size")
        if int(self.index_step) <= 0:
            raise ValueError("ReductionAccumulatorProof requires a positive index_step")
        if self.seed_term_count is not None and int(self.seed_term_count) < 0:
            raise ValueError("ReductionAccumulatorProof requires a non-negative seed_term_count")
        if self.count_parameter_storage_identity_key is not None:
            object.__setattr__(
                self,
                "count_parameter_storage_identity_key",
                _normalize_storage_identity_key(self.count_parameter_storage_identity_key),
            )
        object.__setattr__(self, "constant_bias", _bias_key(int(self.constant_bias), int(self.result_size))[1])
        lane_terms = tuple(
            sorted((int(offset), max(1, int(size or 0))) for offset, size in (self.lane_terms or ()))
        )
        if lane_terms:
            start_offset = int(self.start_offset)
            min_offset = min(offset for offset, _size in lane_terms)
            if start_offset != 0 and min_offset == start_offset:
                lane_terms = tuple((offset - start_offset, size) for offset, size in lane_terms)
            object.__setattr__(self, "lane_terms", lane_terms)
        return_op_refs = tuple(
            sorted(
                (ref for ref in (self.return_op_refs or ()) if isinstance(ref, PcodeOpRef)),
                key=lambda ref: repr(ref.stable_key()),
            )
        )
        object.__setattr__(self, "return_op_refs", return_op_refs)
        return_value_op_refs = tuple(
            sorted(
                (ref for ref in (self.return_value_op_refs or ()) if isinstance(ref, PcodeOpRef)),
                key=lambda ref: repr(ref.stable_key()),
            )
        )
        object.__setattr__(self, "return_value_op_refs", return_value_op_refs)

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        limit_key = _loop_object_key(self.limit_expr)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        side_effect_key = self.side_effect_profile.stable_key()
        if limit_key is None or side_effect_key is None or any(key is None for key in guard_keys):
            return None
        return (
            "reduction_accumulator_proof",
            self.reduction_kind,
            self.pointer_base_ref.stable_key(),
            self.count_parameter_name,
            None if self.count_parameter_index is None else int(self.count_parameter_index),
            self.count_parameter_storage_identity_key,
            limit_key,
            max(1, int(self.result_size)),
            int(self.stride),
            int(self.element_size),
            int(self.start_offset),
            int(self.start_index),
            int(self.index_step),
            int(self.index_scale or self.stride),
            bool(self.signed_counter),
            tuple(term.stable_key() for term in self.seed_terms)
            if tuple(self.seed_terms or ())
            else (
                (("seed_term_count", int(self.seed_term_count)),)
                if self.seed_term_count is not None
                else ()
            ),
            tuple((int(offset), max(1, int(size or 0))) for offset, size in self.lane_terms),
            tuple(witness.stable_key() for witness in self.loop_body_witnesses),
            tuple(witness.stable_key() for witness in self.exact_return_witnesses),
            guard_keys,
            side_effect_key,
            int(self.constant_bias),
            self.induction_phi_ref.stable_key() if self.induction_phi_ref is not None else None,
            self.accumulator_phi_ref.stable_key() if self.accumulator_phi_ref is not None else None,
            self.update_op_ref.stable_key() if self.update_op_ref is not None else None,
            tuple(ref.stable_key() for ref in self.load_op_refs),
            tuple(ref.stable_key() for ref in self.return_op_refs),
            tuple(ref.stable_key() for ref in self.return_value_op_refs),
            self.entry_block_ref.stable_key() if self.entry_block_ref is not None else None,
            self.backedge_block_ref.stable_key() if self.backedge_block_ref is not None else None,
            bool(self.return_region_value_proven),
            self.source,
        )

    def readonly_term_sequence_specificity_score(self) -> int:
        """Relative precision of the proven readonly term-sequence contract.

        A higher score means the proof carries more object-level information
        about non-zero starts, explicit seed terms, or scalarized vector lanes.
        This is used only as an ordering tiebreaker between overlapping
        readonly summaries that target the same base/count reduction surface.
        """

        try:
            start_index = max(0, int(self.start_index))
        except (TypeError, ValueError):
            start_index = 0
        seed_terms = tuple(self.seed_terms or ())
        seed_term_count = self.seed_term_count
        try:
            implicit_seed_count = 0 if seed_term_count is None else max(0, int(seed_term_count))
        except (TypeError, ValueError):
            implicit_seed_count = 0
        lane_terms = tuple(self.lane_terms or ())
        return int(start_index) + len(seed_terms) + int(implicit_seed_count) + len(lane_terms)

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.readonly_term_sequence_contract_key()

    def readonly_term_sequence_contract_key(
        self,
        *,
        result_size: Optional[int] = None,
    ) -> Optional[Tuple[Any, ...]]:
        """Semantic contract for a readonly scalar memory-term reduction.

        The contract is deliberately proof-centric rather than surface-centric:
        it is derived from the accumulator proof's base object, limit object,
        scalarized term geometry, explicit seed terms, and side-effect profile.
        A path-sensitive ``LoopSummaryRef`` may still be comparable through this
        contract when the accumulator proof proves the readonly term sequence;
        loops with writes, calls, escapes, or conditional side effects remain
        proof-required and do not get a shortcut here.
        """

        target_result_size = self._readonly_contract_result_size(result_size)
        if target_result_size is None:
            return None
        if self.side_effect_profile.requires_effect_proof():
            return None
        pointer_key = self.pointer_base_ref.semantic_key()
        count_identity = self.count_parameter_semantic_identity()
        if count_identity is None:
            return None
        limit_key = _loop_summary_limit_semantic_key(self.limit_expr)
        if limit_key is None:
            count_storage_key = _normalize_storage_identity_key(
                self.count_parameter_storage_identity_key
            )
            if count_storage_key is None:
                return None
            limit_key = ("loop_limit_count_storage_identity", count_storage_key)
        side_effect_key = self.side_effect_profile.semantic_key()
        if pointer_key is None or limit_key is None or side_effect_key is None:
            return None
        geometry = self._readonly_contract_scalar_geometry(target_result_size)
        if geometry is None:
            return None
        term_start_offset, scalar_stride = geometry
        seed_terms = self._readonly_contract_seed_terms(
            target_result_size=target_result_size,
            term_start_offset=term_start_offset,
            scalar_stride=scalar_stride,
        )
        if seed_terms is None:
            return None
        canonical_start, remaining_seed_terms = self._readonly_contract_canonical_start_and_seed_terms(
            seed_terms=seed_terms,
            target_result_size=target_result_size,
            term_start_offset=term_start_offset,
            scalar_stride=scalar_stride,
        )
        seed_keys = tuple(term.stable_key() for term in remaining_seed_terms)
        return (
            "readonly_reduction_term_sequence_contract",
            self.reduction_kind,
            pointer_key,
            count_identity,
            limit_key,
            max(1, int(target_result_size)),
            int(canonical_start),
            int(self.index_step),
            int(term_start_offset),
            int(scalar_stride),
            bool(self.signed_counter),
            seed_keys,
            _bias_key(int(self.constant_bias), target_result_size),
            side_effect_key,
        )

    def _readonly_contract_result_size(self, result_size: Optional[int]) -> Optional[int]:
        proof_result_size = max(1, int(self.result_size or 0))
        try:
            target_result_size = proof_result_size if result_size is None else max(1, int(result_size))
        except (TypeError, ValueError):
            return None
        if target_result_size > proof_result_size:
            return None
        if (
            target_result_size < proof_result_size
            and self.reduction_kind not in {"sum", "memory_sum"}
            and not self._readonly_reduction_uses_distinct_term_width()
        ):
            return None
        return target_result_size

    def count_parameter_semantic_identity(self) -> Optional[Tuple[Any, ...]]:
        return _count_parameter_semantic_identity(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def count_parameter_semantic_identities(self) -> Tuple[Tuple[Any, ...], ...]:
        return _count_parameter_semantic_identities(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def _readonly_contract_scalar_geometry(
        self,
        target_result_size: int,
    ) -> Optional[Tuple[int, int]]:
        target_result_size = max(1, int(target_result_size))
        term_access_size = self._readonly_term_access_size()
        start_index = int(self.start_index)
        if start_index < 0:
            return None
        index_scale = int(self.index_scale or self.stride)
        if index_scale <= 0:
            return None
        lane_terms = tuple(self.lane_terms or ())
        if lane_terms:
            scalar_lanes = self._readonly_contract_scalar_lane_terms(target_result_size)
            if not scalar_lanes:
                return None
            first_lane_offset = int(scalar_lanes[0][0])
            scalar_stride = target_result_size
            term_start_offset = int(self.start_offset) + first_lane_offset - start_index * scalar_stride
            return term_start_offset, scalar_stride
        if term_access_size != target_result_size and not self._readonly_reduction_uses_distinct_term_width():
            return None
        term_start_offset = int(self.start_offset) - start_index * index_scale
        return term_start_offset, index_scale

    def _readonly_reduction_uses_distinct_term_width(self) -> bool:
        return str(self.reduction_kind or "").startswith("fp_")

    def _readonly_term_access_size(self) -> int:
        if self._readonly_reduction_uses_distinct_term_width():
            return max(1, int(self.element_size or 0))
        return max(1, int(self.result_size or 0))

    def _readonly_contract_scalar_lane_terms(
        self,
        target_result_size: int,
    ) -> Tuple[Tuple[int, int], ...]:
        target_result_size = max(1, int(target_result_size))
        normalized_lanes = tuple(
            sorted((int(offset), max(1, int(size or 0))) for offset, size in (self.lane_terms or ()))
        )
        if not normalized_lanes:
            return ()
        if int(self.index_step) != 1:
            return ()
        if not all(size == target_result_size for _offset, size in normalized_lanes):
            return ()
        offsets = [offset for offset, _size in normalized_lanes]
        expected_offsets = [offsets[0] + index * target_result_size for index in range(len(offsets))]
        if offsets != expected_offsets:
            return ()
        if int(self.index_scale or self.stride) != target_result_size * len(offsets):
            return ()
        return normalized_lanes

    def _readonly_contract_seed_terms(
        self,
        *,
        target_result_size: int,
        term_start_offset: int,
        scalar_stride: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        target_result_size = max(1, int(target_result_size))
        term_access_size = self._readonly_term_access_size()
        explicit_seed_terms = tuple(self.seed_terms or ())
        if explicit_seed_terms:
            normalized_terms = []
            for term in explicit_seed_terms:
                if max(1, int(getattr(term, "access_size", 0) or 0)) != term_access_size:
                    return None
                normalized_terms.append(
                    ReadonlyReductionTermRef(
                        byte_offset=int(getattr(term, "byte_offset")),
                        access_size=term_access_size,
                    )
                )
            return tuple(normalized_terms)
        seed_term_count = self.seed_term_count
        if seed_term_count is None:
            return ()
        try:
            seed_count = int(seed_term_count)
        except (TypeError, ValueError):
            return None
        if seed_count < 0 or seed_count > int(self.start_index):
            return None
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset) + index * int(scalar_stride),
                access_size=term_access_size,
            )
            for index in range(seed_count)
        )

    def _readonly_contract_canonical_start_and_seed_terms(
        self,
        *,
        seed_terms: Tuple[ReadonlyReductionTermRef, ...],
        target_result_size: int,
        term_start_offset: int,
        scalar_stride: int,
    ) -> Tuple[int, Tuple[ReadonlyReductionTermRef, ...]]:
        term_access_size = self._readonly_term_access_size()
        canonical_start = int(self.start_index)
        index_step = int(self.index_step)
        remaining_seed_terms = sorted(
            tuple(seed_terms or ()),
            key=lambda term: (int(term.byte_offset), int(term.access_size)),
        )
        while remaining_seed_terms:
            previous_index = canonical_start - index_step
            if previous_index < 0:
                break
            expected_term = ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset) + previous_index * int(scalar_stride),
                access_size=term_access_size,
            )
            expected_key = expected_term.stable_key()
            matching_index = None
            for index, term in enumerate(remaining_seed_terms):
                if term.stable_key() == expected_key:
                    matching_index = index
                    break
            if matching_index is None:
                break
            remaining_seed_terms.pop(matching_index)
            canonical_start = previous_index
        return canonical_start, tuple(remaining_seed_terms)

    def trip_count_for_count_value(self, count_value: int) -> Optional[int]:
        if int(count_value) <= 0:
            return None
        start_index = int(self.start_index)
        index_step = int(self.index_step)
        if index_step <= 0:
            return None
        if int(count_value) <= start_index:
            return 0
        distance = int(count_value) - start_index
        return (distance + index_step - 1) // index_step

    def loop_body_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        trip_count = self.trip_count_for_count_value(count_value)
        if trip_count is None:
            return None
        access_size = self._readonly_term_access_size()
        lane_terms = self._scalar_lane_terms(require_witness_prefix=False)
        if lane_terms:
            lane_count = len(lane_terms)
            if lane_count <= 0:
                return None
            stride = int(self.index_scale or self.stride)
            return tuple(
                ReadonlyReductionTermRef(
                    byte_offset=int(self.start_offset)
                    + (scalar_index // lane_count) * stride
                    + lane_terms[scalar_index % lane_count][0],
                    access_size=access_size,
                )
                for scalar_index in range(trip_count)
            )
        if int(self.element_size) != access_size:
            return None
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(self.start_offset) + index * int(self.stride),
                access_size=access_size,
            )
            for index in range(trip_count)
        )

    def full_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        seed_terms = self.seed_terms_for_count_value(count_value)
        if seed_terms is None:
            return None
        if not tuple(self.seed_terms or ()) and self.seed_term_count is not None:
            try:
                if int(count_value) >= int(self.start_index):
                    full_seed_terms = self._materialized_seed_prefix_terms()
                    if full_seed_terms is None:
                        return None
                    seed_terms = full_seed_terms
            except (TypeError, ValueError):
                return None
        loop_terms = self.loop_body_terms_for_count_value(count_value)
        if loop_terms is None:
            return self._prefix_terms_from_exact_return_witnesses(count_value)
        return tuple(seed_terms) + tuple(loop_terms)

    def _prefix_terms_from_exact_return_witnesses(
        self,
        count_value: int,
    ) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        """Materialize a small prefix from stronger exact-return evidence.

        Some optimized shapes prove the broad READONLY_SUM contract but only
        retain exact return witnesses for selected counts, e.g. count=1,3,4.
        If a larger exact witness is a contiguous scalar prefix, every smaller
        prefix is also object-centrically determined.  This deliberately refuses
        non-prefix or non-scalar witnesses; it does not infer arbitrary loop
        behavior from a sparse sample.
        """

        try:
            count_value = int(count_value)
        except (TypeError, ValueError):
            return None
        if count_value <= 0:
            return None
        access_size = self._readonly_term_access_size()
        expected_prefix = tuple(
            ReadonlyReductionTermRef(
                byte_offset=index * access_size,
                access_size=access_size,
            )
            for index in range(count_value)
        )
        expected_prefix_key = tuple(term.stable_key() for term in expected_prefix)
        for witness in sorted(
            tuple(self.exact_return_witnesses or ()),
            key=lambda item: int(getattr(item, "exact_count", 0) or 0),
        ):
            exact_count = int(getattr(witness, "exact_count", 0) or 0)
            terms = tuple(getattr(witness, "terms", ()) or ())
            if exact_count < count_value or len(terms) < exact_count:
                continue
            expected_witness = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=index * access_size,
                    access_size=access_size,
                )
                for index in range(exact_count)
            )
            if tuple(term.stable_key() for term in terms[:exact_count]) != tuple(
                term.stable_key() for term in expected_witness
            ):
                continue
            candidate = tuple(terms[:count_value])
            if tuple(term.stable_key() for term in candidate) == expected_prefix_key:
                return candidate
        return None

    def seed_terms_for_count_value(self, count_value: int) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        seed_terms = tuple(self.seed_terms or ())
        if not seed_terms:
            seed_term_count = self.seed_term_count
            if seed_term_count is not None:
                count_value = int(count_value)
                if count_value <= 0:
                    return None
                start_index = int(self.start_index)
                if start_index <= 0:
                    return ()
                seed_term_count_value = int(seed_term_count)
                if seed_term_count_value < 0 or seed_term_count_value > start_index:
                    return None
                index_scale = int(self.index_scale or self.stride)
                if index_scale <= 0:
                    return None
                if count_value >= start_index:
                    return ()
                term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
                selected_count = min(int(count_value), seed_term_count_value)
                return tuple(
                    ReadonlyReductionTermRef(
                        byte_offset=int(term_start_offset) + index * index_scale,
                        access_size=self._readonly_term_access_size(),
                    )
                    for index in range(selected_count)
                )
            return ()
        count_value = int(count_value)
        if count_value <= 0:
            return None
        start_index = int(self.start_index)
        if count_value >= start_index:
            return seed_terms
        index_scale = int(self.index_scale or self.stride)
        if index_scale <= 0:
            return None
        term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        selected = []
        for term in seed_terms:
            byte_offset = int(term.byte_offset)
            logical_delta = byte_offset - term_start_offset
            if logical_delta < 0 or logical_delta % index_scale != 0:
                return None
            logical_index = logical_delta // index_scale
            if logical_index < count_value:
                selected.append(term)
        return tuple(selected)

    def _materialized_seed_prefix_terms(self) -> Optional[Tuple[ReadonlyReductionTermRef, ...]]:
        seed_terms = tuple(self.seed_terms or ())
        if seed_terms:
            return seed_terms
        seed_term_count = self.seed_term_count
        if seed_term_count is None:
            return ()
        start_index = int(self.start_index)
        if start_index <= 0:
            return ()
        seed_term_count_value = int(seed_term_count)
        if seed_term_count_value < 0 or seed_term_count_value > start_index:
            return None
        index_scale = int(self.index_scale or self.stride)
        if index_scale <= 0:
            return None
        term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        return tuple(
            ReadonlyReductionTermRef(
                byte_offset=int(term_start_offset) + index * index_scale,
                access_size=self._readonly_term_access_size(),
            )
            for index in range(seed_term_count_value)
        )

    def _readonly_lowering_failure_reason(self) -> Optional[str]:
        if self.side_effect_profile.requires_effect_proof():
            return "side_effects_not_representable"
        return None

    def _build_loop_summary_ref(
        self,
        *,
        loop_var_unit_override: Optional[str] = None,
        canonicalize_scalar_iteration: bool = False,
    ) -> Optional["LoopSummaryRef"]:
        if self._readonly_lowering_failure_reason() is not None:
            return None
        stride = int(self.stride)
        element_size = int(self.element_size)
        index_scale = int(self.index_scale or stride)
        if stride <= 0 or element_size <= 0 or index_scale <= 0:
            return None
        lane_terms = tuple(self.lane_terms or ())
        if canonicalize_scalar_iteration:
            scalar_lane_terms = self._scalar_lane_terms(require_witness_prefix=False)
            if scalar_lane_terms:
                access_size = max(1, int(self.result_size))
                stride = access_size
                element_size = access_size
                index_scale = access_size
                lane_terms = ()
                term_start_offset = int(self.start_offset) - int(self.start_index) * access_size
            else:
                term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        else:
            term_start_offset = int(self.start_offset) - int(self.start_index) * index_scale
        return LoopSummaryRef(
            start_expr=_loop_int_expr(int(self.start_index), self.limit_expr),
            limit_expr=self.limit_expr,
            step_expr=_loop_int_expr(int(self.index_step), self.limit_expr),
            term_descriptor=LoopTermDescriptorRef(
                kind="memory_load",
                reduction_kind="sum",
                location_base_ref=self.pointer_base_ref,
                start_offset=term_start_offset,
                stride=index_scale,
                element_size=element_size,
                result_size=max(1, int(self.result_size)),
                lane_terms=lane_terms,
            ),
            seed_terms=tuple(self.seed_terms or ()),
            seed_term_count=None
            if self.seed_term_count is None
            else int(self.seed_term_count),
            witnesses=tuple(self.loop_body_witnesses or ()),
            side_effect_profile=self.side_effect_profile,
            guard_constraints=tuple(self.guard_constraints or ()),
            loop_var_unit=loop_var_unit_override or self.loop_var_unit(),
            source=self.source,
            constant_bias=int(self.constant_bias),
        )

    def lower_to_loop_summary_ref(self) -> Optional["LoopSummaryRef"]:
        return self._build_loop_summary_ref()

    def with_runtime_evidence(
        self,
        *,
        limit_expr: Any,
        result_size: int,
        loop_body_witnesses: Tuple[ReadonlyReductionWitness, ...],
        exact_return_witnesses: Tuple[ReadonlyReductionWitness, ...],
        guard_constraints: Tuple[Any, ...],
        signed_counter: bool,
    ) -> "ReductionAccumulatorProof":
        normalized_result_size = max(1, int(result_size or 0))
        lane_terms = tuple(self.lane_terms or ())
        if not lane_terms:
            lane_terms = self._infer_lane_terms_from_witnesses(
                access_size=normalized_result_size,
                witnesses=tuple(loop_body_witnesses or ()),
            )
        return replace(
            self,
            limit_expr=limit_expr,
            result_size=normalized_result_size,
            lane_terms=lane_terms,
            loop_body_witnesses=tuple(loop_body_witnesses or ()),
            exact_return_witnesses=tuple(exact_return_witnesses or ()),
            guard_constraints=tuple(guard_constraints or ()),
            signed_counter=bool(signed_counter),
        )._normalize_scalar_prefix_from_exact_witnesses()._complete_seed_prefix_from_exact_witnesses()

    def _normalize_scalar_prefix_from_exact_witnesses(self) -> "ReductionAccumulatorProof":
        access_size = max(1, int(self.result_size))
        current_start = max(0, int(self.start_index or 0))
        if (
            access_size <= 0
            or current_start <= 0
            or (
                int(self.stride) == access_size
                and int(self.element_size) == access_size
                and int(self.index_scale or self.stride) == access_size
                and int(self.start_offset) == 0
                and int(self.start_index) == 0
            )
        ):
            return self
        exact_witnesses = {
            int(witness.exact_count): tuple(witness.terms)
            for witness in self.exact_return_witnesses or ()
            if int(getattr(witness, "exact_count", 0) or 0) > 0
        }
        if not exact_witnesses:
            return self
        matching_counts = []
        for count_value, terms in exact_witnesses.items():
            expected_terms = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=index * access_size,
                    access_size=access_size,
                )
                for index in range(count_value)
            )
            if tuple(term.stable_key() for term in terms) == tuple(
                term.stable_key() for term in expected_terms
            ):
                matching_counts.append(int(count_value))
        if not matching_counts:
            return self
        matching_counts = sorted(set(matching_counts))
        prefix_len = 0
        while (prefix_len + 1) in matching_counts:
            prefix_len += 1
        if prefix_len < max(1, current_start):
            return self
        if int(self.start_offset) != current_start * access_size:
            return self
        return replace(
            self,
            stride=access_size,
            element_size=access_size,
            start_offset=0,
            start_index=0,
            index_step=1,
            index_scale=access_size,
            seed_terms=(),
            seed_term_count=None,
            lane_terms=(),
        )

    def _infer_lane_terms_from_witnesses(
        self,
        *,
        access_size: int,
        witnesses: Tuple[ReadonlyReductionWitness, ...],
    ) -> Tuple[Tuple[int, int], ...]:
        stride = int(self.index_scale or self.stride)
        element_size = int(self.element_size)
        if (
            stride <= 0
            or access_size <= 0
            or stride % access_size != 0
            or element_size <= access_size
            or int(self.start_index) != 0
            or int(self.index_step) != 1
        ):
            return ()
        lane_count = stride // access_size
        if lane_count <= 1:
            return ()
        witnesses_by_count = {int(witness.exact_count): tuple(witness.terms) for witness in witnesses or ()}
        for count in range(1, lane_count + 1):
            terms = witnesses_by_count.get(count)
            expected = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=int(self.start_offset) + index * access_size,
                    access_size=access_size,
                )
                for index in range(count)
            )
            if terms is None or tuple(term.stable_key() for term in terms) != tuple(
                term.stable_key() for term in expected
            ):
                return ()
        return tuple((index * access_size, access_size) for index in range(lane_count))

    def lower_to_readonly_reduction(self) -> Optional["ReadonlyReductionLowering"]:
        loop_summary = self.lower_to_loop_summary_ref()
        if loop_summary is None:
            return None
        readonly_ref = ReadonlyReductionRef(
            reduction_kind=self.reduction_kind,
            pointer_base_ref=self.pointer_base_ref,
            count_parameter_name=self.count_parameter_name,
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
            stride=int(self.stride),
            element_size=int(self.element_size),
            result_size=max(1, int(self.result_size)),
            start_offset=int(self.start_offset),
            signed_counter=bool(self.signed_counter),
            source=self.source,
            semantic_witnesses=tuple(self.loop_body_witnesses or ()),
            loop_summary=loop_summary,
            accumulator_proof=self,
            constant_bias=int(self.constant_bias),
        )
        return ReadonlyReductionLowering(
            proof=self,
            loop_summary=loop_summary,
            readonly_reduction=readonly_ref,
        )

    def lower_to_readonly_reduction_ref(self) -> Optional["ReadonlyReductionRef"]:
        lowering = self.lower_to_readonly_reduction()
        return lowering.readonly_reduction if lowering is not None else None

    def loop_var_unit(self) -> str:
        return "scalar_element_index" if self._scalar_lane_terms(require_witness_prefix=True) else "element_index"

    def _scalar_lane_terms(
        self,
        *,
        require_witness_prefix: bool,
    ) -> Tuple[Tuple[int, int], ...]:
        normalized_lanes = tuple(
            sorted((int(offset), max(1, int(size or 0))) for offset, size in (self.lane_terms or ()))
        )
        if not normalized_lanes:
            return ()
        access_size = max(1, int(self.result_size))
        offsets = [offset for offset, _size in normalized_lanes]
        expected_offsets = [index * access_size for index in range(len(offsets))]
        if not all(size == access_size for _offset, size in normalized_lanes):
            return ()
        if offsets != expected_offsets:
            return ()
        if int(self.index_scale or self.stride) != access_size * len(offsets):
            return ()
        if int(self.index_step) != 1:
            return ()
        if require_witness_prefix:
            if int(self.start_index) != 0:
                return ()
            witnesses_by_count = {
                int(witness.exact_count): tuple(witness.terms)
                for witness in self.loop_body_witnesses or ()
            }
            for count in range(1, len(offsets)):
                terms = witnesses_by_count.get(count)
                expected = tuple(
                    ReadonlyReductionTermRef(
                        byte_offset=int(self.start_offset) + index * access_size,
                        access_size=access_size,
                    )
                    for index in range(count)
                )
                if terms is None or tuple(term.stable_key() for term in terms) != tuple(
                    term.stable_key() for term in expected
                ):
                    return ()
        return normalized_lanes

    def _complete_seed_prefix_from_exact_witnesses(self) -> "ReductionAccumulatorProof":
        if tuple(self.seed_terms or ()) or self.seed_term_count is not None:
            return self
        if int(self.start_index or 0) not in {0}:
            return self
        scalar_lane_terms = self._scalar_lane_terms(require_witness_prefix=False)
        if not scalar_lane_terms:
            return self
        access_size = max(1, int(self.result_size))
        first_body_offset = int(self.start_offset) + int(scalar_lane_terms[0][0])
        if first_body_offset <= 0 or first_body_offset % access_size != 0:
            return self
        candidate_start_index = first_body_offset // access_size
        if candidate_start_index <= 0:
            return self
        exact_witnesses = {
            int(witness.exact_count): tuple(witness.terms)
            for witness in self.exact_return_witnesses or ()
        }
        for count_value in range(1, candidate_start_index + 1):
            witness_terms = exact_witnesses.get(count_value)
            if witness_terms is None:
                return self
            expected_terms = tuple(
                ReadonlyReductionTermRef(
                    byte_offset=index * access_size,
                    access_size=access_size,
                )
                for index in range(count_value)
            )
            if tuple(term.stable_key() for term in witness_terms) != tuple(
                term.stable_key() for term in expected_terms
            ):
                return self
        seed_terms = tuple(
            ReadonlyReductionTermRef(
                byte_offset=index * access_size,
                access_size=access_size,
            )
            for index in range(candidate_start_index)
        )
        return replace(
            self,
            start_index=int(candidate_start_index),
            seed_terms=seed_terms,
            seed_term_count=None,
        )

    def json_items(self):
        yield "kind", "reduction_accumulator_proof"
        yield "reduction_kind", self.reduction_kind
        yield "pointer_base_ref", self.pointer_base_ref
        yield "count_parameter_name", self.count_parameter_name
        yield "count_parameter_index", self.count_parameter_index
        yield "count_parameter_storage_identity_key", self.count_parameter_storage_identity_key
        yield "result_size", max(1, int(self.result_size))
        yield "stride", int(self.stride)
        yield "element_size", int(self.element_size)
        yield "start_offset", int(self.start_offset)
        yield "start_index", int(self.start_index)
        yield "index_step", int(self.index_step)
        yield "index_scale", int(self.index_scale or self.stride)
        yield "signed_counter", bool(self.signed_counter)
        yield "seed_terms", each(self.seed_terms)
        yield "seed_term_count", None if self.seed_term_count is None else int(self.seed_term_count)
        yield "lane_terms", each(
            self.lane_terms,
            source_converter(lambda lane: inline(
                ("byte_offset", int(lane[0])),
                ("access_size", max(1, int(lane[1] or 0))),
            )),
        )
        yield "loop_body_witnesses", each(self.loop_body_witnesses)
        yield "exact_return_witnesses", each(self.exact_return_witnesses)
        yield "guard_constraints", each(self.guard_constraints, _loop_object_source)
        yield "side_effect_profile", self.side_effect_profile
        yield "constant_bias", int(self.constant_bias)
        yield "induction_phi_ref", self.induction_phi_ref if self.induction_phi_ref is not None else None
        yield "accumulator_phi_ref", self.accumulator_phi_ref if self.accumulator_phi_ref is not None else None
        yield "update_op_ref", self.update_op_ref if self.update_op_ref is not None else None
        yield "load_op_refs", each(self.load_op_refs)
        yield "return_op_refs", each(self.return_op_refs)
        yield "return_value_op_refs", each(self.return_value_op_refs)
        yield "entry_block_ref", self.entry_block_ref if self.entry_block_ref is not None else None
        yield "backedge_block_ref", self.backedge_block_ref if self.backedge_block_ref is not None else None
        yield "return_region_value_proven", bool(self.return_region_value_proven)
        yield "source", self.source

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReadonlyReductionRef:
    """Structured identity for a readonly pointer-reduction summary."""

    reduction_kind: str
    pointer_base_ref: LocationBaseRef
    count_parameter_name: str
    count_parameter_index: Optional[int] = None
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]] = None
    stride: int = 0
    element_size: int = 0
    result_size: int = 0
    start_offset: int = 0
    signed_counter: bool = True
    source: str = "recurrence_summary"
    semantic_witnesses: Tuple[ReadonlyReductionWitness, ...] = ()
    loop_summary: Optional[LoopSummaryRef] = None
    accumulator_proof: Optional[ReductionAccumulatorProof] = None
    constant_bias: int = 0

    def __post_init__(self) -> None:
        result_size = max(1, int(self.result_size or 0))
        ref_bias = _bias_key(int(self.constant_bias), result_size)[1]
        loop_summary = self.loop_summary
        accumulator_proof = self.accumulator_proof
        if self.count_parameter_storage_identity_key is not None:
            object.__setattr__(
                self,
                "count_parameter_storage_identity_key",
                _normalize_storage_identity_key(self.count_parameter_storage_identity_key),
            )
        source_biases = []
        if loop_summary is not None:
            summary_result_size_raw = int(
                getattr(getattr(loop_summary, "term_descriptor", None), "result_size", 0) or 0
            )
            if summary_result_size_raw > 0 and summary_result_size_raw != result_size:
                raise ValueError("ReadonlyReductionRef.result_size must match loop_summary term result_size")
            if summary_result_size_raw <= 0 and int(getattr(loop_summary, "constant_bias", 0) or 0) != 0:
                raise ValueError("ReadonlyReductionRef cannot align biased loop_summary without term result_size")
            summary_result_size = result_size if summary_result_size_raw <= 0 else summary_result_size_raw
            summary_bias = _bias_key(
                int(getattr(loop_summary, "constant_bias", 0) or 0),
                summary_result_size,
            )[1]
            source_biases.append(("loop_summary.constant_bias", summary_bias))
        if accumulator_proof is not None:
            proof_result_size = max(1, int(getattr(accumulator_proof, "result_size", 0) or 0))
            if proof_result_size != result_size:
                raise ValueError("ReadonlyReductionRef.result_size must match accumulator_proof.result_size")
            proof_bias = _bias_key(
                int(getattr(accumulator_proof, "constant_bias", 0) or 0),
                proof_result_size,
            )[1]
            source_biases.append(("accumulator_proof.constant_bias", proof_bias))
        nonzero_source_biases = [bias for _name, bias in source_biases if bias != 0]
        if ref_bias == 0 and nonzero_source_biases:
            ref_bias = nonzero_source_biases[0]
        for name, source_bias in source_biases:
            if ref_bias != source_bias:
                raise ValueError(f"ReadonlyReductionRef.constant_bias must match {name}")
        object.__setattr__(self, "constant_bias", ref_bias)

    def stable_key(self) -> Tuple[Any, ...]:
        loop_summary_key = self.loop_summary.stable_key() if self.loop_summary is not None else None
        proof_key = self.accumulator_proof.stable_key() if self.accumulator_proof is not None else None
        return (
            "readonly_reduction",
            self.reduction_kind,
            self.pointer_base_ref.stable_key(),
            self.count_parameter_name,
            None if self.count_parameter_index is None else int(self.count_parameter_index),
            self.count_parameter_storage_identity_key,
            int(self.stride),
            int(self.element_size),
            int(self.result_size),
            int(self.start_offset),
            bool(self.signed_counter),
            self.source,
            loop_summary_key,
            proof_key,
            _bias_key(int(self.constant_bias), self.result_size),
        )

    def display_name(self) -> str:
        return (
            f"{self.reduction_kind}("
            f"{self.pointer_base_ref.display_name()},"
            f"{self.count_parameter_name},"
            f"stride={int(self.stride)},"
            f"elem={int(self.element_size)},"
            f"bias={int(self.constant_bias)})"
        )

    def readonly_term_sequence_contract_key(
        self,
        *,
        result_size: Optional[int] = None,
    ) -> Optional[Tuple[Any, ...]]:
        ref_result_size = max(1, int(self.result_size or 0))
        try:
            target_result_size = ref_result_size if result_size is None else max(1, int(result_size))
        except (TypeError, ValueError):
            return None
        if target_result_size > ref_result_size:
            return None
        if self.accumulator_proof is not None:
            proof_key_fn = getattr(self.accumulator_proof, "readonly_term_sequence_contract_key", None)
            if callable(proof_key_fn):
                try:
                    proof_key = proof_key_fn(result_size=target_result_size)
                except (AttributeError, TypeError, ValueError):
                    proof_key = None
                if proof_key is not None:
                    return proof_key
        if self.loop_summary is not None:
            if result_size is not None and target_result_size != ref_result_size:
                return loop_summary_method_b_key_at_result_size(
                    self.loop_summary,
                    target_result_size,
                )
            loop_key_fn = getattr(self.loop_summary, "pairwise_semantic_key", None)
            if callable(loop_key_fn):
                try:
                    loop_key = loop_key_fn()
                except (AttributeError, TypeError, ValueError):
                    loop_key = None
                if loop_key is not None:
                    return loop_key
        return None

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        proof_key = (
            self.readonly_term_sequence_contract_key()
            if self.accumulator_proof is not None
            else None
        )
        if proof_key is not None:
            pointer_identity = self.pointer_base_ref.semantic_key()
            count_identity = self.count_parameter_semantic_identity()
            if pointer_identity is None or count_identity is None:
                return None
            return (
                "readonly_reduction_proof_semantic",
                self.reduction_kind,
                pointer_identity,
                count_identity,
                max(1, int(self.result_size or 0)),
                _bias_key(int(self.constant_bias), self.result_size),
                proof_key,
            )
        if self.loop_summary is not None:
            loop_key = self.loop_summary.semantic_key()
            if loop_key is None:
                return None
            pointer_identity = self.pointer_base_ref.semantic_key()
            count_identity = self.count_parameter_semantic_identity()
            if pointer_identity is None or count_identity is None:
                return None
            return (
                "readonly_reduction_loop_semantic",
                self.reduction_kind,
                pointer_identity,
                count_identity,
                max(1, int(self.result_size or 0)),
                _bias_key(int(self.constant_bias), self.result_size),
                loop_key,
            )
        witness_prefix = self._semantic_witness_prefix(required_prefix=3, cap=3)
        if witness_prefix is None:
            return None
        pointer_identity = self.pointer_base_ref.semantic_key()
        count_identity = self.count_parameter_semantic_identity()
        if pointer_identity is None or count_identity is None:
            return None
        return (
            "readonly_reduction_semantic",
            self.reduction_kind,
            pointer_identity,
            count_identity,
            max(1, int(self.result_size or 0)),
            int(self.start_offset),
            _bias_key(int(self.constant_bias), self.result_size),
            tuple(witness.stable_key() for witness in witness_prefix),
        )

    def count_parameter_semantic_identity(self) -> Optional[Tuple[Any, ...]]:
        return _count_parameter_semantic_identity(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def count_parameter_semantic_identities(self) -> Tuple[Tuple[Any, ...], ...]:
        return _count_parameter_semantic_identities(
            count_parameter_index=self.count_parameter_index,
            count_parameter_storage_identity_key=self.count_parameter_storage_identity_key,
        )

    def _count_parameter_semantic_identity(self) -> Optional[Tuple[Any, ...]]:
        return self.count_parameter_semantic_identity()

    def readonly_term_sequence_specificity_score(self) -> int:
        """Relative precision of this readonly reduction contract."""

        if self.accumulator_proof is not None:
            score_fn = getattr(
                self.accumulator_proof,
                "readonly_term_sequence_specificity_score",
                None,
            )
            if callable(score_fn):
                try:
                    return max(0, int(score_fn()))
                except (TypeError, ValueError):
                    return 0
        witness_counts = {
            int(witness.exact_count)
            for witness in (self.semantic_witnesses or ())
            if getattr(witness, "exact_count", None) is not None
        }
        return len(witness_counts)

    def _semantic_witness_prefix(
        self,
        *,
        required_prefix: int,
        cap: Optional[int] = None,
    ) -> Optional[Tuple[ReadonlyReductionWitness, ...]]:
        if not self.semantic_witnesses:
            return None
        witnesses_by_count = {
            int(witness.exact_count): witness
            for witness in self.semantic_witnesses
            if int(getattr(witness, "exact_count", 0) or 0) > 0
        }
        prefix = []
        next_count = 1
        while next_count in witnesses_by_count:
            prefix.append(witnesses_by_count[next_count])
            if cap is not None and len(prefix) >= int(cap):
                break
            next_count += 1
        if len(prefix) < max(1, int(required_prefix or 0)):
            return None
        return tuple(prefix)

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.loop_summary is not None and self.loop_summary.pairwise_exact_key() is None:
            return None
        return self.stable_key()

    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def pairwise_requires_guard_equivalence(self) -> bool:
        return False

    def json_items(self):
        yield "kind", "readonly_reduction"
        yield "reduction_kind", self.reduction_kind
        yield "pointer_base_ref", self.pointer_base_ref
        yield "count_parameter_name", self.count_parameter_name
        yield "count_parameter_index", self.count_parameter_index
        yield "count_parameter_storage_identity_key", self.count_parameter_storage_identity_key
        yield "stride", int(self.stride)
        yield "element_size", int(self.element_size)
        yield "result_size", int(self.result_size)
        yield "start_offset", int(self.start_offset)
        yield "signed_counter", bool(self.signed_counter)
        yield "source", self.source
        yield "semantic_witnesses", each(self.semantic_witnesses)
        yield "loop_summary", self.loop_summary if self.loop_summary is not None else None
        yield "accumulator_proof", self.accumulator_proof if self.accumulator_proof is not None else None
        yield "constant_bias", int(self.constant_bias)
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class ReadonlyReductionLowering:
    """Materialized readonly lowering produced from a reduction proof."""

    proof: ReductionAccumulatorProof
    loop_summary: LoopSummaryRef
    readonly_reduction: ReadonlyReductionRef
    lowering_kind: str = "readonly_reduction"

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        proof_key = self.proof.stable_key()
        loop_key = self.loop_summary.stable_key()
        readonly_key = self.readonly_reduction.stable_key()
        if proof_key is None or loop_key is None:
            return None
        return (
            "readonly_reduction_lowering",
            self.lowering_kind,
            proof_key,
            loop_key,
            readonly_key,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        proof_key = self.proof.semantic_key()
        loop_key = self.loop_summary.semantic_key()
        readonly_key = self.readonly_reduction.semantic_key()
        if proof_key is None or loop_key is None or readonly_key is None:
            return None
        return (
            "readonly_reduction_lowering_semantic",
            self.lowering_kind,
            proof_key,
            loop_key,
            readonly_key,
        )

    def json_items(self):
        yield "kind", "readonly_reduction_lowering"
        yield "lowering_kind", self.lowering_kind
        yield "proof", self.proof
        yield "loop_summary", self.loop_summary
        yield "readonly_reduction", self.readonly_reduction

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.runtime_refs.loops import (
    LoopTermDescriptorRef,
    _bias_key,
    _count_parameter_semantic_identities,
    _count_parameter_semantic_identity,
    _loop_int_expr,
    _loop_object_key,
    _loop_object_source,
    _loop_object_to_dict,
    _loop_summary_limit_semantic_key,
    _normalize_storage_identity_key,
    loop_summary_method_b_key_at_result_size,
)
