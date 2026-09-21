"""Canonical, proof-free contracts for recurrence-summary promotion.

The objects in this module deliberately contain no runtime/P-code objects and
no proof status.  They are the immutable boundary between extraction and the
unary proof runtime.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Any, Mapping, Sequence, Tuple

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType


RECURRENCE_UNARY_DOMAIN = "recurrence_summary_v1"
RECURRENCE_PREMISE_CODEC_ID = "recurrence_digest_codec_v1"
FUNCTION_UNARY_PREMISE_SCHEMA_ID = "function_unary_premise_v2"


class RecurrenceDigestCodec:
    """Tagged canonical JSON codec; rejects lossy or process-local values."""

    @classmethod
    def freeze(cls, value: Any) -> Any:
        if value is None:
            return ["none"]
        if isinstance(value, bool):
            return ["bool", value]
        if isinstance(value, int):
            return ["int", str(value)]
        if isinstance(value, str):
            return ["str", value]
        if isinstance(value, float):
            raise TypeError("recurrence contracts do not admit floating-point values")
        if isinstance(value, tuple):
            return ["tuple", [cls.freeze(item) for item in value]]
        if isinstance(value, list):
            return ["list", [cls.freeze(item) for item in value]]
        if isinstance(value, Mapping):
            if not all(isinstance(key, str) for key in value):
                raise TypeError("recurrence contract mappings require string keys")
            return [
                "map",
                [[key, cls.freeze(value[key])] for key in sorted(value)],
            ]
        if isinstance(value, (set, frozenset)):
            raise TypeError("recurrence contracts do not admit unordered sets")
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            return cls.freeze(stable_key())
        raise TypeError(f"opaque recurrence contract value: {type(value).__qualname__}")

    @classmethod
    def canonical_bytes(cls, domain_tag: str, value: Any) -> bytes:
        if not isinstance(domain_tag, str) or not domain_tag:
            raise ValueError("recurrence digest domain tag is required")
        payload = ["recurrence_digest_envelope_v1", domain_tag, cls.freeze(value)]
        return json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")

    @classmethod
    def digest(cls, domain_tag: str, value: Any) -> str:
        return hashlib.sha256(cls.canonical_bytes(domain_tag, value)).hexdigest()


_ALLOWED_EXPRESSION_TYPES = frozenset({
    ExpressionType.CONSTANT,
    ExpressionType.PARAMETER,
    ExpressionType.BINARY_OP,
    ExpressionType.UNARY_OP,
    ExpressionType.INTRINSIC,
})

_ALLOWED_BINARY_OPERATORS = frozenset({
    "INT_ADD", "INT_SUB", "INT_MULT", "INT_AND", "INT_OR", "INT_XOR",
    "INT_LEFT", "INT_RIGHT", "INT_SRIGHT", "INT_EQUAL", "INT_NOTEQUAL",
    "INT_LESS", "INT_LESSEQUAL", "INT_SLESS", "INT_SLESSEQUAL",
    "BOOL_AND", "BOOL_OR", "BOOL_XOR", "PIECE", "SUBPIECE",
})
_ALLOWED_UNARY_OPERATORS = frozenset({
    "INT_2COMP", "INT_NEGATE", "INT_ZEXT", "INT_SEXT", "BOOL_NEGATE",
})
_BOOLEAN_OPERATORS = frozenset({
    "INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", "INT_LESSEQUAL",
    "INT_SLESS", "INT_SLESSEQUAL", "BOOL_AND", "BOOL_OR", "BOOL_XOR",
    "BOOL_NEGATE",
})
_SIGNED_OPERATORS = frozenset({"INT_SLESS", "INT_SLESSEQUAL", "INT_SRIGHT", "INT_SEXT"})
_UNSIGNED_OPERATORS = frozenset({"INT_LESS", "INT_LESSEQUAL", "INT_RIGHT", "INT_ZEXT"})
_ALLOWED_RECURRENCE_RUNTIME_REFS = frozenset({
    "LoopSummaryRef", "CountedLoopSummaryRef", "ComposedLoopSummaryRef",
    "StateTransitionLoopSummaryRef", "CountedStateTransitionLoopSummaryRef",
})
_ALLOWED_RECURRENCE_INTRINSICS = {
    4098: "COUNTED_LOOP_SUM",
    4099: "STATE_TRANSITION_LOOP_COUNT",
    4100: "COUNTED_STATE_TRANSITION_VALUE",
}


def _tuple_tree(value: Any) -> Any:
    if isinstance(value, (tuple, list)):
        return tuple(_tuple_tree(item) for item in value)
    return value


@dataclass(frozen=True)
class CanonicalRecurrenceRuntimeRef:
    type_tag: str
    identity: Tuple[Any, ...]

    def stable_key(self) -> Tuple[Any, ...]:
        return self.identity


@dataclass(frozen=True)
class ImmutableRecurrenceExpression:
    kind: str
    size: int
    value: Any = None
    operator: str = ""
    parameter_index: int = -1
    operands: Tuple["ImmutableRecurrenceExpression", ...] = ()
    intrinsic_identity: Tuple[Any, ...] = ()
    sort: str = "bitvector"
    signedness: str = "signless"
    constant_width_bits: int = 0
    storage_identity: Tuple[Any, ...] = ()
    runtime_ref_type: str = ""
    provenance: Tuple[Any, ...] = ()

    def __post_init__(self) -> None:
        self._validate()

    def _validate(self) -> None:
        allowed_kinds = {item.name for item in _ALLOWED_EXPRESSION_TYPES}
        if self.kind not in allowed_kinds:
            raise ValueError("serialized recurrence expression kind is unsupported")
        if not isinstance(self.size, int) or self.size <= 0:
            raise ValueError("recurrence expression width must be positive")
        if self.sort not in {"bool", "bitvector"}:
            raise ValueError("serialized recurrence expression sort is unsupported")
        if self.signedness not in {"signed", "unsigned", "signless"}:
            raise ValueError("serialized recurrence signedness is unsupported")
        if not isinstance(self.operands, tuple) or not all(
            isinstance(item, ImmutableRecurrenceExpression) for item in self.operands
        ):
            raise TypeError("serialized recurrence operands must be typed expressions")
        if (
            not isinstance(self.provenance, tuple)
            or len(self.provenance) != 3
            or self.provenance[0] != "recurrence_expression_provenance_v1"
            or not isinstance(self.provenance[1], tuple)
            or len(self.provenance[1]) != 2
            or self.provenance[1][0] != "data_type"
            or not isinstance(self.provenance[2], tuple)
            or len(self.provenance[2]) != 2
            or self.provenance[2][0] != "opcode"
            or not isinstance(self.provenance[2][1], int)
        ):
            raise ValueError("serialized recurrence provenance is invalid")

        if self.kind == ExpressionType.CONSTANT.name:
            if (
                self.operands or self.operator or self.parameter_index != -1
                or self.intrinsic_identity or self.runtime_ref_type
            ):
                raise ValueError("serialized recurrence constant shape is invalid")
            if self.sort == "bool":
                if not isinstance(self.value, bool) or self.constant_width_bits != 1:
                    raise ValueError("serialized recurrence bool constant is invalid")
            else:
                width = self.size * 8
                if (
                    isinstance(self.value, bool)
                    or not isinstance(self.value, int)
                    or self.constant_width_bits != width
                    or not 0 <= self.value < (1 << width)
                ):
                    raise ValueError("serialized recurrence bit-vector constant is invalid")
            return
        if self.kind == ExpressionType.PARAMETER.name:
            if (
                self.operands or self.operator or self.value is not None
                or self.parameter_index < 0 or self.sort != "bitvector"
                or self.constant_width_bits != 0
                or self.intrinsic_identity or self.runtime_ref_type
            ):
                raise ValueError("serialized recurrence parameter shape is invalid")
            return

        if self.value is not None or self.parameter_index != -1 or self.constant_width_bits != 0:
            raise ValueError("serialized recurrence non-leaf payload is invalid")
        if self.kind == ExpressionType.BINARY_OP.name:
            if self.operator not in _ALLOWED_BINARY_OPERATORS or len(self.operands) != 2:
                raise ValueError("serialized recurrence binary operator or arity is invalid")
        elif self.kind == ExpressionType.UNARY_OP.name:
            if self.operator not in _ALLOWED_UNARY_OPERATORS or len(self.operands) != 1:
                raise ValueError("serialized recurrence unary operator or arity is invalid")
        elif self.kind == ExpressionType.INTRINSIC.name:
            if (
                self.operator != "typed_recurrence_intrinsic"
                or not self.operands
                or self.runtime_ref_type not in _ALLOWED_RECURRENCE_RUNTIME_REFS
                or not isinstance(self.intrinsic_identity, tuple)
                or not self.intrinsic_identity
            ):
                raise ValueError("serialized recurrence intrinsic identity is invalid")
            opcode_items = tuple(
                item for item in self.provenance
                if isinstance(item, tuple) and len(item) == 2 and item[0] == "opcode"
            )
            if len(opcode_items) != 1 or int(opcode_items[0][1]) not in _ALLOWED_RECURRENCE_INTRINSICS:
                raise ValueError("serialized recurrence intrinsic opcode is invalid")
        if self.kind != ExpressionType.INTRINSIC.name and (
            self.intrinsic_identity or self.runtime_ref_type
        ):
            raise ValueError("serialized recurrence runtime reference tag is misplaced")
        expected_sort = "bool" if self.operator in _BOOLEAN_OPERATORS else "bitvector"
        if self.sort != expected_sort:
            raise ValueError("serialized recurrence operator/sort mismatch")
        expected_signedness = (
            "signed" if self.operator in _SIGNED_OPERATORS
            else "unsigned" if self.operator in _UNSIGNED_OPERATORS
            else "signless"
        )
        if self.signedness != expected_signedness:
            raise ValueError("serialized recurrence operator/signedness mismatch")

    @classmethod
    def from_stable_key(cls, value: Any) -> "ImmutableRecurrenceExpression":
        value = _tuple_tree(value)
        if not isinstance(value, tuple) or len(value) != 14 or value[0] != "recurrence_expression_v2":
            raise ValueError("serialized recurrence expression stable key is invalid")
        return cls(
            str(value[1]), int(value[2]), value[3], str(value[4]), int(value[5]),
            tuple(cls.from_stable_key(item) for item in value[6]),
            _tuple_tree(value[7]), str(value[8]), str(value[9]), int(value[10]),
            _tuple_tree(value[11]), str(value[12]), _tuple_tree(value[13]),
        )

    @classmethod
    def from_expression(cls, expression: Expression) -> "ImmutableRecurrenceExpression":
        if not isinstance(expression, Expression):
            raise TypeError("recurrence expression must be an Expression")
        if expression.expr_type not in _ALLOWED_EXPRESSION_TYPES:
            raise ValueError(f"unsupported recurrence expression kind: {expression.expr_type.name}")
        if int(expression.size or 0) <= 0:
            raise ValueError("recurrence expression width must be positive")
        operands = tuple(cls.from_expression(item) for item in expression.operands)
        width_bits = int(expression.size) * 8
        if expression.expr_type == ExpressionType.CONSTANT:
            if not isinstance(expression.value, (bool, int)):
                raise ValueError("recurrence constants must be integer bit-vectors")
            if isinstance(expression.value, bool):
                value = bool(expression.value)
                sort = "bool"
                constant_width_bits = 1
            else:
                value = int(expression.value) & ((1 << width_bits) - 1)
                sort = "bitvector"
                constant_width_bits = width_bits
            parameter_index = -1
        elif expression.expr_type == ExpressionType.PARAMETER:
            if not isinstance(expression.value, int) or int(expression.value) < 0:
                raise ValueError("recurrence parameters require a stable non-negative index")
            value = None
            parameter_index = int(expression.value)
            sort = "bitvector"
            constant_width_bits = 0
        else:
            value = None
            parameter_index = -1
            sort = "bool" if str(expression.operator or "") in _BOOLEAN_OPERATORS else "bitvector"
            constant_width_bits = 0
        operator = str(expression.operator or "")
        if expression.expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP} and not operator:
            raise ValueError("recurrence operator is required")
        expected_arity = 2 if expression.expr_type == ExpressionType.BINARY_OP else 1
        if expression.expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP} and len(operands) != expected_arity:
            raise ValueError("recurrence expression arity mismatch")
        if expression.expr_type == ExpressionType.BINARY_OP and operator not in _ALLOWED_BINARY_OPERATORS:
            raise ValueError(f"unsupported recurrence binary operator: {operator}")
        if expression.expr_type == ExpressionType.UNARY_OP and operator not in _ALLOWED_UNARY_OPERATORS:
            raise ValueError(f"unsupported recurrence unary operator: {operator}")
        intrinsic_identity: Tuple[Any, ...] = ()
        runtime_ref_type = ""
        if expression.expr_type == ExpressionType.INTRINSIC:
            if not operands:
                raise ValueError("recurrence intrinsic requires typed operands")
            runtime_ref = getattr(expression, "runtime_ref", None)
            runtime_ref_type = type(runtime_ref).__name__ if runtime_ref is not None else ""
            if runtime_ref_type not in _ALLOWED_RECURRENCE_RUNTIME_REFS:
                raise ValueError("recurrence intrinsic requires an allowed typed runtime reference")
            stable_key = getattr(runtime_ref, "stable_key", None)
            if callable(stable_key):
                intrinsic_identity = stable_key()
            if not isinstance(intrinsic_identity, tuple) or not intrinsic_identity:
                raise ValueError("recurrence intrinsic typed identity is required")
            opcode = int(expression.opcode) if expression.opcode is not None else -1
            if _ALLOWED_RECURRENCE_INTRINSICS.get(opcode) != str(expression.name or ""):
                raise ValueError("recurrence intrinsic opcode/mnemonic pair is not allowed")
            operator = operator or "typed_recurrence_intrinsic"
        if expression.expr_type in {ExpressionType.CONSTANT, ExpressionType.PARAMETER} and operands:
            raise ValueError("recurrence leaf expression has operands")
        storage_identity: Tuple[Any, ...] = ()
        storage = getattr(expression, "storage_info", None)
        if storage is not None:
            register_key = getattr(storage, "register_identity_key", lambda: None)()
            if register_key is not None:
                storage_identity = tuple(register_key)
            else:
                storage_identity = (
                    "storage", str(getattr(storage, "space_name", "")),
                    int(getattr(storage, "space_id", -1) or -1),
                    int(getattr(storage, "offset", 0) or 0),
                    int(getattr(storage, "size_bits", 0) or 0),
                )
        if operator in _SIGNED_OPERATORS:
            signedness = "signed"
        elif operator in _UNSIGNED_OPERATORS:
            signedness = "unsigned"
        else:
            signedness = "signless"
        provenance = (
            "recurrence_expression_provenance_v1",
            ("data_type", str(getattr(expression, "data_type", None) or "")),
            ("opcode", int(expression.opcode) if expression.opcode is not None else -1),
        )
        return cls(
            expression.expr_type.name,
            int(expression.size),
            value,
            operator,
            parameter_index,
            operands,
            intrinsic_identity,
            sort,
            signedness,
            constant_width_bits,
            storage_identity,
            runtime_ref_type,
            provenance,
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "recurrence_expression_v2", self.kind, self.size, self.value,
            self.operator, self.parameter_index,
            tuple(item.stable_key() for item in self.operands),
            self.intrinsic_identity,
            self.sort, self.signedness, self.constant_width_bits,
            self.storage_identity, self.runtime_ref_type, self.provenance,
        )

    def to_dict(self) -> Mapping[str, Any]:
        return {
            "kind": self.kind, "size": self.size, "value": self.value,
            "operator": self.operator, "parameter_index": self.parameter_index,
            "operands": [item.to_dict() for item in self.operands],
            "intrinsic_identity": self.intrinsic_identity,
            "sort": self.sort, "signedness": self.signedness,
            "constant_width_bits": self.constant_width_bits,
            "storage_identity": self.storage_identity,
            "runtime_ref_type": self.runtime_ref_type,
            "provenance": self.provenance,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ImmutableRecurrenceExpression":
        if not isinstance(payload, Mapping):
            raise TypeError("recurrence expression payload must be a mapping")
        allowed_fields = {
            "kind", "size", "value", "operator", "parameter_index", "operands",
            "intrinsic_identity", "sort", "signedness", "constant_width_bits",
            "storage_identity", "runtime_ref_type", "provenance",
        }
        if set(payload).difference(allowed_fields):
            raise ValueError("serialized recurrence expression has unknown fields")
        value = cls(
            kind=str(payload["kind"]), size=int(payload["size"]),
            value=payload.get("value"), operator=str(payload.get("operator") or ""),
            parameter_index=int(payload.get("parameter_index", -1)),
            operands=tuple(cls.from_dict(item) for item in payload.get("operands", ())),
            intrinsic_identity=_tuple_tree(payload.get("intrinsic_identity", ())),
            sort=str(payload.get("sort") or ""),
            signedness=str(payload.get("signedness") or ""),
            constant_width_bits=int(payload.get("constant_width_bits", 0)),
            storage_identity=_tuple_tree(payload.get("storage_identity", ())),
            runtime_ref_type=str(payload.get("runtime_ref_type") or ""),
            provenance=_tuple_tree(payload.get("provenance", ())),
        )
        return value

    def materialize(self) -> Expression:
        operands = [item.materialize() for item in self.operands]
        expr_type = ExpressionType[self.kind]
        runtime_ref = None
        opcode = None
        name = None
        if expr_type == ExpressionType.INTRINSIC:
            runtime_ref = CanonicalRecurrenceRuntimeRef(
                self.runtime_ref_type, self.intrinsic_identity
            )
            for candidate_opcode, candidate_name in _ALLOWED_RECURRENCE_INTRINSICS.items():
                if self.provenance and tuple(self.provenance)[-1] == ("opcode", candidate_opcode):
                    opcode, name = candidate_opcode, candidate_name
                    break
            if opcode is None:
                raise ValueError("serialized recurrence intrinsic opcode is unavailable")
        expression = Expression(
            expr_type, value=self.value if expr_type == ExpressionType.CONSTANT else (
                self.parameter_index if expr_type == ExpressionType.PARAMETER else None
            ), operator=self.operator or None, operands=operands, size=self.size,
            name=name, runtime_ref=runtime_ref, opcode=opcode,
            recurrence_semantic_key=self.stable_key(),
        )
        return expression


@dataclass(frozen=True)
class ImmutableRecurrenceCondition:
    expression: ImmutableRecurrenceExpression
    negated: bool

    @classmethod
    def from_condition(cls, condition: Condition) -> "ImmutableRecurrenceCondition":
        if not isinstance(condition, Condition):
            raise TypeError("recurrence guard must be a Condition")
        return cls(
            ImmutableRecurrenceExpression.from_expression(condition.expression),
            bool(condition.negated),
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return ("recurrence_condition_v1", self.expression.stable_key(), self.negated)

    @classmethod
    def from_stable_key(cls, value: Any) -> "ImmutableRecurrenceCondition":
        value = _tuple_tree(value)
        if (
            not isinstance(value, tuple) or len(value) != 3
            or value[0] != "recurrence_condition_v1" or not isinstance(value[2], bool)
        ):
            raise ValueError("serialized recurrence condition stable key is invalid")
        return cls(ImmutableRecurrenceExpression.from_stable_key(value[1]), value[2])


@dataclass(frozen=True)
class RetainedExactReturnRef:
    identity_key: Tuple[Any, ...]
    payload_digest: str

    def stable_key(self) -> Tuple[Any, ...]:
        return ("retained_exact_return_ref_v1", self.identity_key, self.payload_digest)


@dataclass(frozen=True)
class RecurrenceSeedCore:
    function_identity: Tuple[Any, ...]
    active_precondition_key: Tuple[Any, ...]
    retained_exact_returns: Tuple[RetainedExactReturnRef, ...]
    effect_surface_key: Tuple[Any, ...]
    schema_version: str = "recurrence_seed_core_v1"

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.function_identity, self.active_precondition_key,
            tuple(item.stable_key() for item in self.retained_exact_returns),
            self.effect_surface_key,
        )

    @property
    def digest(self) -> str:
        return RecurrenceDigestCodec.digest(self.schema_version, self.stable_key())


@dataclass(frozen=True)
class QuarantinedRecurrenceReturn:
    guard: Tuple[ImmutableRecurrenceCondition, ...]
    value: ImmutableRecurrenceExpression
    candidate_id: Tuple[Any, ...]
    transition_evidence_key: Tuple[Any, ...]

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "quarantined_recurrence_return_v1",
            tuple(item.stable_key() for item in self.guard), self.value.stable_key(),
            self.candidate_id, self.transition_evidence_key,
        )


@dataclass(frozen=True)
class QuarantinedRecurrenceProposal:
    seed_core_digest: str
    pattern_kind: str
    new_returns: Tuple[QuarantinedRecurrenceReturn, ...]
    retained_exact_return_refs: Tuple[RetainedExactReturnRef, ...]
    schema_version: str = "quarantined_recurrence_proposal_v1"

    def __post_init__(self) -> None:
        def ordered(items: Sequence[Any], tag: str) -> Tuple[Any, ...]:
            return tuple(sorted(
                tuple(items),
                key=lambda item: RecurrenceDigestCodec.canonical_bytes(tag, item.stable_key()),
            ))

        new_returns = ordered(self.new_returns, "recurrence_return_sort_v1")
        retained = ordered(
            self.retained_exact_return_refs, "retained_exact_return_sort_v1"
        )
        candidate_ids = tuple(item.candidate_id for item in new_returns)
        semantic_keys = tuple(item.stable_key() for item in new_returns)
        retained_ids = tuple(item.identity_key for item in retained)
        retained_keys = tuple(item.stable_key() for item in retained)
        if len(set(candidate_ids)) != len(candidate_ids):
            raise ValueError("recurrence proposal has duplicate candidate ids")
        if len(set(semantic_keys)) != len(semantic_keys):
            raise ValueError("recurrence proposal has duplicate semantic returns")
        if len(set(retained_ids)) != len(retained_ids) or len(set(retained_keys)) != len(retained_keys):
            raise ValueError("recurrence proposal has duplicate retained exact returns")
        if set(candidate_ids).intersection(retained_ids):
            raise ValueError("recurrence proposal exact/summary identity collision")
        object.__setattr__(self, "new_returns", new_returns)
        object.__setattr__(self, "retained_exact_return_refs", retained)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.seed_core_digest, self.pattern_kind,
            tuple(item.stable_key() for item in self.new_returns),
            tuple(item.stable_key() for item in self.retained_exact_return_refs),
        )

    @property
    def digest(self) -> str:
        return RecurrenceDigestCodec.digest(self.schema_version, self.stable_key())


def function_recurrence_binding_digest(
    seed_core_digest: str,
    proposal_digest: str,
    function_unary_premise_digest: str,
) -> str:
    return RecurrenceDigestCodec.digest(
        "function_recurrence_binding_v1",
        (seed_core_digest, proposal_digest, function_unary_premise_digest),
    )


def semantic_recurrence_closure_digest(
    function_recurrence_binding: str,
    requirement_keys: Sequence[Tuple[Any, ...]],
    proof_result_digest: str,
    dependency_subproof_digests: Sequence[str],
) -> str:
    if not proof_result_digest or not dependency_subproof_digests:
        raise ValueError("recurrence closure requires content-bound proof evidence")
    return RecurrenceDigestCodec.digest(
        "semantic_recurrence_closure_v2",
        (
            function_recurrence_binding,
            tuple(requirement_keys),
            proof_result_digest,
            tuple(dependency_subproof_digests),
        ),
    )


_RECURRENCE_SUBPROOF_KINDS = (
    "candidate_validation", "transition_termination", "overlap",
    "partition_coverage", "effect_surface",
)

_RECURRENCE_SUBPROOF_METHODS = {
    "candidate_validation": "summary_return_candidate_validator_v2",
    "transition_termination": "typed_recurrence_transition_termination_validator_v2",
    "overlap": "condition_smt_overlap_validator_v2",
    "partition_coverage": "condition_smt_partition_totality_v2",
    "effect_surface": "recurrence_effect_surface_validator_v2",
}

_TRANSITION_PROPOSITION_TAGS = frozenset({
    "unit_step_affine_recursion_v1",
    "affine_counted_loop_v1",
    "guarded_affine_decreasing_state_v1",
    "affine_counted_state_transition_v1",
    "base_member_bound_to_transition_v1",
})


@dataclass(frozen=True)
class RecurrenceSMTQueryReceipt:
    query_role: str
    normalized_condition_keys: Tuple[Any, ...]
    width_sort_precondition_key: Tuple[Any, ...]
    solver: str
    result_status: str
    query_digest: str = ""
    schema_version: str = "recurrence_smt_query_receipt_v1"

    def __post_init__(self) -> None:
        if self.schema_version != "recurrence_smt_query_receipt_v1":
            raise ValueError("recurrence SMT query receipt version is not allowed")
        if self.query_role not in {
            "overlap_feasibility", "overlap_value_inequality",
            "partition_coverage_miss",
        }:
            raise ValueError("recurrence SMT query role is not allowed")
        if not isinstance(self.normalized_condition_keys, tuple) or not self.normalized_condition_keys:
            raise ValueError("recurrence SMT query conditions are missing")
        for condition_key in self.normalized_condition_keys:
            ImmutableRecurrenceCondition.from_stable_key(condition_key)
        expected_surface = (
            "overlap_query_surface_v1"
            if self.query_role.startswith("overlap_")
            else "coverage_query_surface_v1"
        )
        if (
            not isinstance(self.width_sort_precondition_key, tuple)
            or len(self.width_sort_precondition_key) < 3
            or self.width_sort_precondition_key[0] != expected_surface
        ):
            raise ValueError("recurrence SMT width/sort/precondition surface is invalid")
        if self.query_role.startswith("overlap_"):
            if (
                len(self.width_sort_precondition_key) != 5
                or not isinstance(self.width_sort_precondition_key[1], str)
                or not self.width_sort_precondition_key[1]
                or not isinstance(self.width_sort_precondition_key[4], tuple)
            ):
                raise ValueError("recurrence overlap query surface is invalid")
            _validate_width_sort_key(self.width_sort_precondition_key[2])
            _validate_width_sort_key(self.width_sort_precondition_key[3])
            for condition_key in self.width_sort_precondition_key[4]:
                ImmutableRecurrenceCondition.from_stable_key(condition_key)
        else:
            if (
                len(self.width_sort_precondition_key) != 4
                or not isinstance(self.width_sort_precondition_key[1], str)
                or not isinstance(self.width_sort_precondition_key[2], tuple)
                or not self.width_sort_precondition_key[2]
                or not isinstance(self.width_sort_precondition_key[3], tuple)
            ):
                raise ValueError("recurrence coverage query surface is invalid")
            for width_sort in self.width_sort_precondition_key[2]:
                _validate_width_sort_key(width_sort)
            for condition_key in self.width_sort_precondition_key[3]:
                ImmutableRecurrenceCondition.from_stable_key(condition_key)
        if self.solver != "z3" or self.result_status not in {"sat", "unsat"}:
            raise ValueError("recurrence SMT solver result is not allowed")
        expected = RecurrenceDigestCodec.digest(
            self.schema_version,
            (
                self.query_role,
                self.normalized_condition_keys,
                self.width_sort_precondition_key,
                self.solver,
                self.result_status,
            ),
        )
        if self.query_digest and self.query_digest != expected:
            raise ValueError("recurrence SMT query digest mismatch")
        object.__setattr__(self, "query_digest", expected)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version,
            self.query_role,
            self.normalized_condition_keys,
            self.width_sort_precondition_key,
            self.solver,
            self.result_status,
            self.query_digest,
        )

    @classmethod
    def from_stable_key(cls, value: Any) -> "RecurrenceSMTQueryReceipt":
        value = _tuple_tree(value)
        if not isinstance(value, tuple) or len(value) != 7:
            raise ValueError("recurrence SMT query receipt schema is invalid")
        schema, role, conditions, surface, solver, status, digest = value
        return cls(
            str(role), _tuple_tree(conditions), _tuple_tree(surface),
            str(solver), str(status), str(digest), str(schema),
        )


def _validate_width_sort_key(value: Any) -> None:
    if (
        not isinstance(value, tuple)
        or len(value) != 4
        or value[0] != "width_sort_v1"
        or not isinstance(value[1], int)
        or value[1] <= 0
        or value[2] not in {"bitvec", "bool"}
        or value[3] not in {"signed", "unsigned", "neutral"}
    ):
        raise ValueError("recurrence width/sort identity is invalid")


def _is_semantic_identity(value: Any) -> bool:
    return (isinstance(value, str) and bool(value)) or (
        isinstance(value, tuple) and bool(value)
    )


def _validate_transition_proposition(value: Any) -> None:
    if (
        not isinstance(value, tuple) or len(value) != 3
        or value[0] != "candidate_transition_v2"
        or not _is_semantic_identity(value[1])
        or not isinstance(value[2], tuple)
    ):
        raise ValueError("recurrence transition proposition is not allowed")
    inner = value[2]
    if not inner or inner[0] not in _TRANSITION_PROPOSITION_TAGS:
        raise ValueError("recurrence transition proposition is not allowed")
    tag = inner[0]
    if tag == "unit_step_affine_recursion_v1":
        evidence = inner[1] if len(inner) == 2 else None
        fields = dict(
            item for item in tuple(evidence[1:] if isinstance(evidence, tuple) else ())
            if isinstance(item, tuple) and len(item) == 2
        )
        valid = (
            isinstance(evidence, tuple) and evidence
            and evidence[0] == "linear_self_recursion_transition_evidence_v1"
            and fields.get("step") in {-1, 1}
            and fields.get("effect_profile") == "single_direct_self_call_no_store"
            and fields.get("termination_measure") in {
                "signed_unit_decrement_to_bound", "signed_unit_increment_to_bound",
            }
            and isinstance(fields.get("width"), int) and fields["width"] > 0
        )
    elif tag == "affine_counted_loop_v1":
        valid = (
            len(inner) == 5 and isinstance(inner[1], int) and inner[1] != 0
            and isinstance(inner[2], bool) and isinstance(inner[3], tuple)
            and inner[3] and set(inner[3]).issubset({1, 2, 4})
            and isinstance(inner[4], tuple) and inner[4]
        )
    elif tag == "guarded_affine_decreasing_state_v1":
        valid = (
            len(inner) == 4 and isinstance(inner[1], bool)
            and isinstance(inner[2], tuple) and inner[2]
            and all(isinstance(item, int) and item > 0 for item in inner[2])
            and isinstance(inner[3], int) and inner[3] > 0
        )
    elif tag == "affine_counted_state_transition_v1":
        valid = len(inner) == 3 and isinstance(inner[1], int) and inner[1] != 0 and isinstance(inner[2], bool)
    else:
        valid = (
            len(inner) == 3 and inner[1] == value[1]
            and isinstance(inner[2], tuple) and bool(inner[2])
        )
    if not valid:
        raise ValueError("recurrence transition proposition schema is invalid")


def _validate_subproof_proposition(proof_kind: str, value: Any) -> None:
    if not isinstance(value, tuple):
        raise ValueError("recurrence subproof proposition must be a tuple")
    if proof_kind == "candidate_validation":
        if len(value) != 4 or value[0] != "candidate_validation_v2" or not all(
            isinstance(item, str) and item for item in value[1:3]
        ) or not isinstance(value[3], tuple) or not value[3]:
            raise ValueError("recurrence candidate proposition schema is invalid")
        for candidate in value[3]:
            if (
                not isinstance(candidate, tuple) or len(candidate) != 7
                or candidate[0] != "candidate_v2"
                or not _is_semantic_identity(candidate[1])
                or not all(isinstance(item, tuple) and item for item in candidate[2:5])
                or not isinstance(candidate[6], tuple) or len(candidate[6]) != 2
                or candidate[6][0] != "active_precondition_digest_v1"
                or not isinstance(candidate[6][1], str) or not candidate[6][1]
            ):
                raise ValueError("recurrence candidate identity schema is invalid")
            guard = candidate[2]
            if len(guard) != 2 or guard[0] != "guard_conditions_v1" or not isinstance(guard[1], tuple):
                raise ValueError("recurrence candidate guard schema is invalid")
            for condition_key in guard[1]:
                ImmutableRecurrenceCondition.from_stable_key(condition_key)
            ImmutableRecurrenceExpression.from_stable_key(candidate[3])
            transition = candidate[4]
            if (
                len(transition) != 3 or transition[0] != "transition_evidence_digest_v1"
                or transition[1] not in {
                    "linear_self_recursion_transition_evidence_v1",
                    "counted_loop_transition_evidence",
                    "state_transition_loop_evidence",
                    "state_transition_loop_evidence_with_zero_iteration_anchor",
                }
                or not isinstance(transition[2], str) or not transition[2]
            ):
                raise ValueError("recurrence candidate transition identity is invalid")
            _validate_width_sort_key(candidate[5])
        return
    if proof_kind == "transition_termination":
        if (
            len(value) != 4 or value[0] != "transition_termination_v2"
            or not isinstance(value[1], str) or not value[1]
            or not isinstance(value[2], tuple) or not value[2]
            or not isinstance(value[3], tuple) or not value[3]
        ):
            raise ValueError("recurrence transition proof schema is invalid")
        for proposition in value[2]:
            _validate_transition_proposition(proposition)
        for surface in value[3]:
            if not isinstance(surface, tuple) or len(surface) != 3 or surface[0] != "candidate_surface_v1":
                raise ValueError("recurrence transition surface schema is invalid")
            _validate_width_sort_key(surface[2])
        return
    if proof_kind == "overlap":
        if len(value) != 3 or value[0] != "overlap_unsat_v2" or not isinstance(value[1], str) or not value[1]:
            raise ValueError("recurrence overlap proposition schema is invalid")
        receipts = tuple(RecurrenceSMTQueryReceipt.from_stable_key(item) for item in value[2])
        if not receipts or any(not item.query_role.startswith("overlap_") for item in receipts):
            raise ValueError("recurrence overlap query receipts are incomplete")
        comparison_ids = {item.width_sort_precondition_key[1] for item in receipts}
        for comparison_id in comparison_ids:
            if not any(
                item.width_sort_precondition_key[1] == comparison_id
                and item.result_status == "unsat"
                for item in receipts
            ):
                raise ValueError("recurrence overlap comparison lacks an UNSAT result")
        return
    if proof_kind == "partition_coverage":
        if len(value) != 3 or value[0] != "partition_coverage_unsat_v2" or not isinstance(value[1], str) or not value[1]:
            raise ValueError("recurrence coverage proposition schema is invalid")
        receipts = tuple(RecurrenceSMTQueryReceipt.from_stable_key(item) for item in value[2])
        if len(receipts) != 1 or receipts[0].query_role != "partition_coverage_miss" or receipts[0].result_status != "unsat":
            raise ValueError("recurrence coverage proof requires one UNSAT query receipt")
        return
    if len(value) != 3 or value[0] != "effect_surface_v2" or not isinstance(value[1], str) or not value[1]:
        raise ValueError("recurrence effect proposition schema is invalid")
    if not isinstance(value[2], tuple) or not value[2]:
        raise ValueError("recurrence effect proposition is empty")
    for effect in value[2]:
        if not isinstance(effect, tuple) or len(effect) != 7 or effect[0] != "candidate_effect_v1":
            raise ValueError("recurrence effect surface schema is invalid")
        expected_tags = (
            "effect_region", "memory_reads", "memory_writes", "call_effect",
            "ub_assumptions",
        )
        if not _is_semantic_identity(effect[1]) or any(
            not isinstance(item, tuple) or not item or item[0] != expected_tag
            for item, expected_tag in zip(effect[2:], expected_tags)
        ):
            raise ValueError("recurrence effect surface identity is invalid")


@dataclass(frozen=True)
class RecurrenceSubproofEvidence:
    proof_kind: str
    proposition_key: Tuple[Any, ...]
    proof_method: str
    disposition: str = "proved"
    dependencies: Tuple[str, ...] = ()
    schema_version: str = "recurrence_subproof_evidence_v2"

    def __post_init__(self) -> None:
        if self.schema_version != "recurrence_subproof_evidence_v2":
            raise ValueError("recurrence subproof evidence version is not allowed")
        if self.proof_kind not in _RECURRENCE_SUBPROOF_KINDS:
            raise ValueError("recurrence subproof kind is not allowed")
        if self.disposition != "proved" or not self.proposition_key or not self.proof_method:
            raise ValueError("recurrence subproof is not a completed typed proof")
        if self.proof_method != _RECURRENCE_SUBPROOF_METHODS[self.proof_kind]:
            raise ValueError("recurrence subproof method is not allowed")
        _validate_subproof_proposition(self.proof_kind, self.proposition_key)
        if not isinstance(self.dependencies, tuple) or any(
            not isinstance(item, str) or not item for item in self.dependencies
        ):
            raise ValueError("recurrence subproof dependency digest is invalid")

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.proof_kind, self.proposition_key,
            self.proof_method, self.disposition, self.dependencies,
        )

    @property
    def digest(self) -> str:
        return RecurrenceDigestCodec.digest(self.schema_version, self.stable_key())

    def to_dict(self) -> Mapping[str, Any]:
        return {
            "proof_kind": self.proof_kind,
            "proposition_key": self.proposition_key,
            "proof_method": self.proof_method,
            "disposition": self.disposition,
            "dependencies": self.dependencies,
            "schema_version": self.schema_version,
            "digest": self.digest,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "RecurrenceSubproofEvidence":
        if not isinstance(payload, Mapping):
            raise TypeError("recurrence subproof payload must be a mapping")
        if set(payload) != {
            "proof_kind", "proposition_key", "proof_method", "disposition",
            "dependencies", "schema_version", "digest",
        }:
            raise ValueError("recurrence subproof payload fields are not allowed")
        item = cls(
            str(payload.get("proof_kind") or ""),
            _tuple_tree(payload.get("proposition_key", ())),
            str(payload.get("proof_method") or ""),
            str(payload.get("disposition") or ""),
            _tuple_tree(payload.get("dependencies", ())),
            str(payload.get("schema_version") or ""),
        )
        if str(payload.get("digest") or "") != item.digest:
            raise ValueError("recurrence subproof digest mismatch")
        return item


@dataclass(frozen=True)
class RecurrenceValidationEvidence:
    seed_core_digest: str
    proposal_digest: str
    function_recurrence_binding_digest: str
    subproofs: Tuple[RecurrenceSubproofEvidence, ...]
    schema_version: str = "recurrence_validation_evidence_v2"

    def __post_init__(self) -> None:
        if self.schema_version != "recurrence_validation_evidence_v2":
            raise ValueError("recurrence validation evidence version is not allowed")
        if not all((
            self.seed_core_digest, self.proposal_digest,
            self.function_recurrence_binding_digest,
        )):
            raise ValueError("recurrence validation binding is incomplete")
        if tuple(item.proof_kind for item in self.subproofs) != _RECURRENCE_SUBPROOF_KINDS:
            raise ValueError("recurrence validation proof allowlist is incomplete or unordered")
        known = set()
        expected_dependencies = {
            "candidate_validation": (),
            "transition_termination": (self.subproofs[0].digest,),
            "overlap": (self.subproofs[0].digest, self.subproofs[1].digest),
            "partition_coverage": (self.subproofs[2].digest,),
            "effect_surface": (self.subproofs[0].digest,),
        }
        for item in self.subproofs:
            if any(dependency not in known for dependency in item.dependencies):
                raise ValueError("recurrence validation dependency DAG is invalid")
            if item.dependencies != expected_dependencies[item.proof_kind]:
                raise ValueError("recurrence validation dependency schema is invalid")
            known.add(item.digest)
        propositions = {item.proof_kind: item.proposition_key for item in self.subproofs}
        proposal_bindings = (
            propositions["candidate_validation"][2],
            propositions["transition_termination"][1],
            propositions["overlap"][1],
            propositions["partition_coverage"][1],
            propositions["effect_surface"][1],
        )
        if any(binding != self.proposal_digest for binding in proposal_bindings):
            raise ValueError("recurrence subproof proposal binding mismatch")
        candidate_records = propositions["candidate_validation"][3]
        candidate_ids = {item[1] for item in candidate_records}
        transition_wrappers = propositions["transition_termination"][2]
        transition_ids = {item[1] for item in transition_wrappers}
        transition_surface_ids = {
            item[1] for item in propositions["transition_termination"][3]
        }
        effect_ids = {item[1] for item in propositions["effect_surface"][2]}
        if not (
            candidate_ids == transition_ids == transition_surface_ids == effect_ids
        ):
            raise ValueError("recurrence subproof candidate binding mismatch")
        candidate_transition = {item[1]: item[4] for item in candidate_records}
        for wrapper in transition_wrappers:
            inner = wrapper[2]
            if inner[0] not in {
                "unit_step_affine_recursion_v1", "base_member_bound_to_transition_v1",
            }:
                continue
            raw_evidence = inner[1] if inner[0] == "unit_step_affine_recursion_v1" else inner[2]
            identity = candidate_transition[wrapper[1]]
            if (
                identity[1] != raw_evidence[0]
                or identity[2] != RecurrenceDigestCodec.digest(
                    "recurrence_transition_evidence_v1", raw_evidence
                )
            ):
                raise ValueError("recurrence transition evidence binding mismatch")

    @property
    def dependency_subproof_digests(self) -> Tuple[str, ...]:
        return tuple(item.digest for item in self.subproofs)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.seed_core_digest, self.proposal_digest,
            self.function_recurrence_binding_digest,
            tuple(item.stable_key() for item in self.subproofs),
        )

    @property
    def proof_result_digest(self) -> str:
        return RecurrenceDigestCodec.digest(self.schema_version, self.stable_key())

    def to_dict(self) -> Mapping[str, Any]:
        return {
            "seed_core_digest": self.seed_core_digest,
            "proposal_digest": self.proposal_digest,
            "function_recurrence_binding_digest": self.function_recurrence_binding_digest,
            "subproofs": [item.to_dict() for item in self.subproofs],
            "schema_version": self.schema_version,
            "proof_result_digest": self.proof_result_digest,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "RecurrenceValidationEvidence":
        if not isinstance(payload, Mapping):
            raise TypeError("recurrence validation payload must be a mapping")
        if set(payload) != {
            "seed_core_digest", "proposal_digest",
            "function_recurrence_binding_digest", "subproofs",
            "schema_version", "proof_result_digest",
        }:
            raise ValueError("recurrence validation payload fields are not allowed")
        evidence = cls(
            str(payload.get("seed_core_digest") or ""),
            str(payload.get("proposal_digest") or ""),
            str(payload.get("function_recurrence_binding_digest") or ""),
            tuple(RecurrenceSubproofEvidence.from_dict(item) for item in payload.get("subproofs", ())),
            str(payload.get("schema_version") or ""),
        )
        if str(payload.get("proof_result_digest") or "") != evidence.proof_result_digest:
            raise ValueError("recurrence proof result digest mismatch")
        return evidence
