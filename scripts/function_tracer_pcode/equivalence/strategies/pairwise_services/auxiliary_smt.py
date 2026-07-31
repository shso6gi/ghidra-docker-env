"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    ConditionSMTOracle,
    Expression,
    ExpressionType,
    Mapping,
    SolverStatus,
    UnknownReasonId,
    Z3Solver,
    build_condition_only_query,
    build_normalized_inequality_query,
    build_pair_query,
    build_parameter_semantic_constraints,
    build_single_case_condition_query,
    build_unknown_recovery_actions,
    collect_float_predicate_smt_declarations,
    collect_intrinsic_smt_declarations,
    collect_unknown_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_node_has_unsupported_smt_ops,
    expression_uses_smt_float_theory,
    expression_uses_smt_uf,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
    save_unknown_query,
    smt_logic_name,
    solve_query_internal,
    solve_query_twostage,
    try_solver_proven_rewrite_equivalence,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__merge_completed_recovery_proofs_from_solver_analyses(
    analysis1: FunctionReturnAnalysis,
    solver_analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    solver_analysis2: FunctionReturnAnalysis,
) -> None:
    for target, source in (
        (analysis1, solver_analysis1),
        (analysis2, solver_analysis2),
    ):
        source_records = [
            dict(record)
            for record in getattr(source, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(record, Mapping)
        ]
        if not source_records:
            continue
        target_records = [
            dict(record)
            for record in getattr(target, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(record, Mapping)
        ]
        existing_ids = {record.get("proof_obligation_id") for record in target_records}
        changed = False
        for record in source_records:
            proof_id = record.get("proof_obligation_id")
            if proof_id is not None and proof_id in existing_ids:
                continue
            target_records.append(record)
            if proof_id is not None:
                existing_ids.add(proof_id)
            changed = True
        if changed:
            target.completed_recovery_proof_evidence = tuple(target_records)

def _impl__solve_query_twostage(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> QueryResult:
    return solve_query_twostage(
        self,
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )

def _impl__record_completed_method_b_dual_summary_solver_proof_if_safe(
    self,
    reason_record,
    analysis: FunctionReturnAnalysis,
    case1: ReturnCase,
    case2: ReturnCase,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    from ...v2.loop_recurrence import LOOP_REASON_SPECS

    if reason_record.reason_id not in LOOP_REASON_SPECS:
        return
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not self._method_b_closure_target_is_specific(object_target_key):
        return
    relation = self._normalize_nested_tuple(object_target_key[4])
    relation_fields = {
        item[0]: item[1]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) == 2
    } if isinstance(relation, tuple) and len(relation) >= 2 else {}
    if relation_fields.get("kind") != "dual_summary":
        return
    left_ref = self._method_b_summary_runtime_ref(getattr(case1, "value_expr", None))
    right_ref = self._method_b_summary_runtime_ref(getattr(case2, "value_expr", None))
    if left_ref is None or right_ref is None:
        return
    left_profile = self._method_b_summary_profile_key(left_ref)
    right_profile = self._method_b_summary_profile_key(right_ref)
    if relation_fields.get("left_summary") != left_profile or relation_fields.get("right_summary") != right_profile:
        return
    if not self._case_pair_loop_summaries_solver_equivalent(
        left_ref,
        right_ref,
        left_case=case1,
        right_case=case2,
    ):
        return
    actions = tuple(build_unknown_recovery_actions([reason_record]))
    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    changed = False
    for action in actions:
        proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
        if proof_id is None or proof_id in existing_ids:
            continue
        proof_content = self._method_b_dual_summary_solver_proof_content(
            action.proof_stage,
            object_target_key=object_target_key,
            left_profile=left_profile,
            right_profile=right_profile,
        )
        if proof_content is None:
            continue
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": reason_record.reason_id,
                "proof_kind": action.proof_kind,
                "recovery_proof_kind": action.proof_kind,
                "proof_stage": action.proof_stage,
                "evidence_kind": action.evidence_kind,
                "required_evidence": tuple(action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_id,
                "proof_source": "method_b_dual_summary_case_local_solver_equality",
                "proof_content": proof_content,
            }
        )
        existing_ids.add(proof_id)
        changed = True
    if changed:
        analysis.completed_recovery_proof_evidence = tuple(records)

def _impl__method_b_dual_summary_solver_proof_content(
    self,
    proof_stage: str,
    *,
    object_target_key: Tuple[Any, ...],
    left_profile: Tuple[Any, ...],
    right_profile: Tuple[Any, ...],
) -> Optional[Dict[str, Any]]:
    common = {
        "object_derived": True,
        "object_target_key": object_target_key,
        "relation_kind": "dual_summary",
        "left_summary": left_profile,
        "right_summary": right_profile,
        "summary_value_equivalence": "unsat",
        "solver_equality_proof": "unsat",
        "guard_coverage": "proven",
        "seed_compensation": "vacuous",
        "term_sequence": "proven",
        "pure_side_effect_profile": "proven",
    }
    if proof_stage == "method_b_covering_case":
        return common
    if proof_stage == "method_b_guard_partition":
        return {
            **common,
            "guard_partition": "proven",
            "partition_coverage_proof": "covered",
        }
    return None

def _impl__solver_rewrite_candidate_object_target_key(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
) -> Tuple[Any, ...]:
    """Object-derived target key for solver rewrite candidate generation."""

    return (
        "solver_rewrite_candidate",
        ("pair", pair_id),
        ("rewrite_stage", "rewrite_candidate_generation"),
        self._solver_rewrite_side_object_key(
            "left",
            base_ctx.get("analysis1"),
            case1,
        ),
        self._solver_rewrite_side_object_key(
            "right",
            base_ctx.get("analysis2"),
            case2,
        ),
    )

def _impl__solver_rewrite_proof_object_target_key(
    self,
    *,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    pair_id: str,
    rewrite_side: str,
    original_expr: Any,
    rewritten_expr: Any,
    rewrite_label: str,
) -> Tuple[Any, ...]:
    """Object-derived target key for solver rewrite proof recheck backlog."""

    return (
        "solver_rewrite_proof",
        ("pair", pair_id),
        ("rewrite_side", rewrite_side),
        ("rewrite_stage", rewrite_label),
        self._solver_rewrite_side_object_key(
            "left",
            base_ctx.get("analysis1"),
            case1,
        ),
        self._solver_rewrite_side_object_key(
            "right",
            base_ctx.get("analysis2"),
            case2,
        ),
        ("original_expression", self._expression_runtime_object_key(original_expr)),
        ("rewritten_expression", self._expression_runtime_object_key(rewritten_expr)),
    )

def _impl__solver_rewrite_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
    case: ReturnCase,
) -> Tuple[Any, ...]:
    target = (
        "solver_rewrite_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._return_storage_object_key(analysis) if analysis is not None else None,
        self._return_case_partition_member_object_key(
            case,
            getattr(case, "return_info", None),
        ),
        ("typed_expression_key", self._expression_runtime_object_key(getattr(case, "value_expr", None))),
        (
            "guards",
            tuple(
                self._return_condition_object_key(condition)
                for condition in (getattr(case, "conditions", None) or ())
            ),
        ),
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__expression_uses_float_or_float_op(expr: Any) -> bool:
    if expr is None:
        return False
    try:
        if expression_uses_smt_float_theory(expr):
            return True
    except (AttributeError, TypeError, RecursionError):
        pass
    expr_type = getattr(expr, "expr_type", None)
    type_name = str(getattr(expr_type, "name", "") or "")
    operator = str(getattr(expr, "operator", "") or "")
    name = str(getattr(expr, "name", "") or "")
    if any(token in type_name.upper() for token in ("FLOAT", "F")):
        return True
    if any(token in operator.upper() for token in ("FLOAT", "FADD", "FSUB", "FMUL", "FDIV")):
        return True
    if name.lower() in {"log", "exp", "sqrt", "sin", "cos", "pow"}:
        return True
    for operand in getattr(expr, "operands", []) or ():
        if _impl__expression_uses_float_or_float_op(operand):
            return True
    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        for condition, value in expr.value:
            if condition is not None and _impl__expression_uses_float_or_float_op(condition.expression):
                return True
            if _impl__expression_uses_float_or_float_op(value):
                return True
    return False

def _impl__unsupported_smt_op_keys(self, expr: Any) -> Tuple[Any, ...]:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return ()
    result: List[Tuple[Any, ...]] = []
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__
    if expr_type == expr_kind.CALL:
        result.append(
            (
                "unsupported_smt_op",
                "CALL",
                str(getattr(expr, "name", "") or "<anonymous>"),
                None,
            )
        )
    elif expr_type in {expr_kind.BINARY_OP, expr_kind.UNARY_OP}:
        if expression_node_has_unsupported_smt_ops(expr):
            result.append(
                (
                    "unsupported_smt_op",
                    expr_type.name,
                    str(getattr(expr, "operator", "") or "<missing>"),
                    None,
                )
            )
    elif expr_type == expr_kind.INTRINSIC:
        if expression_node_has_unsupported_smt_ops(expr):
            result.append(
                (
                    "unsupported_smt_op",
                    "INTRINSIC",
                    str(getattr(expr, "name", "") or "<anonymous>"),
                    None if getattr(expr, "opcode", None) is None else int(getattr(expr, "opcode")),
                )
            )
    for operand in getattr(expr, "operands", []) or []:
        result.extend(self._unsupported_smt_op_keys(operand))
    if expr_type == expr_kind.PHI and expr.value:
        for condition, value in expr.value:
            if condition is not None:
                result.extend(self._unsupported_smt_op_keys(condition.expression))
            result.extend(self._unsupported_smt_op_keys(value))
    return tuple(result)

def _impl__build_nonnegative_query(
    self,
    expr: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
    width_bits: int,
) -> Optional[str]:
    declarations = [f"(set-logic {self._auxiliary_smt_logic([expr], conditions)})"]
    symbol_infos = self._build_auxiliary_parameter_infos(parameters)
    for symbol in symbol_infos:
        declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")

    intrinsic_declarations: List[str] = []
    for item in [expr, *(condition.expression for condition in conditions or [] if condition is not None)]:
        for declaration in collect_intrinsic_smt_declarations(item):
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
    declarations.extend(intrinsic_declarations)
    declarations.extend(self._collect_auxiliary_float_declarations([expr], conditions))

    assertions = []
    assertions.extend(build_parameter_semantic_constraints(symbol_infos))
    for condition in conditions or []:
        if condition is None:
            continue
        rendered_condition = self._render_auxiliary_smt(condition, parameters)
        if rendered_condition is None:
            return None
        assertions.append(f"(assert {rendered_condition})")
    expr_smt = self._render_auxiliary_smt(expr, parameters)
    if expr_smt is None:
        return None
    assertions.append(f"(assert (= ((_ extract {width_bits - 1} {width_bits - 1}) {expr_smt}) #b1))")
    return "\n".join(declarations + assertions + ["(check-sat)"])

def _impl__collect_intrinsic_parameter_specs(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
    *exprs: Expression,
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> Optional[List[Dict[str, Any]]]:
    specs: Dict[Tuple[object, ...], Dict[str, Any]] = {}
    unresolved_symbol = False
    semantic_by_index = self._auxiliary_semantic_hints_by_index(semantic_parameter_sources)

    def add_spec(identity: Optional[Tuple[object, ...]], candidate: Dict[str, Any]) -> None:
        if identity is None:
            return
        size = max(1, int(candidate.get("size", 0) or 4))
        self._apply_auxiliary_semantic_hint(candidate, size=size, semantic_by_index=semantic_by_index)
        existing = specs.get(identity)
        if existing is None:
            specs[identity] = {
                **candidate,
                "identity": identity,
                "size": size,
            }
            return
        if int(existing.get("size", 0) or 0) < size:
            existing.update(candidate)
            existing["identity"] = identity
            existing["size"] = size

    for case in (left_case, right_case):
        for parameter in list(getattr(case, "parameters", None) or []):
            candidate = dict(parameter)
            candidate["name"] = str(parameter.get("name") or "")
            add_spec(parameter_identity_key_from_descriptor(candidate), candidate)

    def visit(expr: Optional[Expression]) -> None:
        nonlocal unresolved_symbol
        if expr is None:
            return
        if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
            identity = parameter_identity_key_from_expression(expr)
            if identity is None:
                unresolved_symbol = True
                return
            candidate = {
                "name": str(getattr(expr, "name", None) or ""),
                "index": int(getattr(expr, "value", -1) or -1),
                "size": max(1, int(getattr(expr, "size", 0) or 4)),
                "data_type": getattr(expr, "data_type", None),
                "is_signed": self._expression_prefers_signed_extension(expr),
                "storage_info": getattr(expr, "storage_info", None),
            }
            add_spec(identity, candidate)
            return
        if getattr(expr, "expr_type", None) == ExpressionType.VARIABLE:
            unresolved_symbol = True
            return
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            for cond, branch_value in getattr(expr, "value", None) or []:
                if cond is not None:
                    visit(getattr(cond, "expression", None))
                visit(branch_value)
            return
        for operand in getattr(expr, "operands", None) or []:
            visit(operand)

    for expr in exprs:
        visit(expr)
    if unresolved_symbol:
        return None

    ordered = sorted(
        specs.values(),
        key=lambda item: (
            self._auxiliary_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    )
    for ordinal, spec in enumerate(ordered):
        spec["aux_name"] = f"aux_param_{ordinal}"
        spec["aux_index"] = ordinal
    return ordered

def _impl__prove_intrinsic_equivalence_under_conditions(
    self,
    left: Expression,
    right: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
    *,
    timeout: int = 2,
) -> bool:
    query = self._build_intrinsic_equivalence_query(left, right, conditions, parameters)
    if not query:
        return False
    result = Z3Solver(timeout=max(1, int(timeout)), debug=self.debug).check_equivalence_direct(query)
    return result.status == SolverStatus.UNSAT

def _impl__build_intrinsic_equivalence_query(
    self,
    left: Expression,
    right: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> Optional[str]:
    if left is None or right is None:
        return None
    declarations = [f"(set-logic {self._auxiliary_smt_logic([left, right], conditions)})"]
    symbol_infos = self._build_auxiliary_parameter_infos(parameters)
    for symbol in symbol_infos:
        declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")
    semantic_constraints = build_parameter_semantic_constraints(symbol_infos)

    intrinsic_declarations: List[str] = []
    for expr in (left, right):
        for declaration in collect_intrinsic_smt_declarations(expr):
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
        for name, bit_width in collect_unknown_smt_declarations(expr):
            declaration = f"(declare-const {name} (_ BitVec {int(bit_width)}))"
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
    for condition in conditions or []:
        if condition is None:
            continue
        for declaration in collect_intrinsic_smt_declarations(condition.expression):
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
        for name, bit_width in collect_unknown_smt_declarations(condition.expression):
            declaration = f"(declare-const {name} (_ BitVec {int(bit_width)}))"
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
    declarations.extend(intrinsic_declarations)
    declarations.extend(self._collect_auxiliary_float_declarations([left, right], conditions))

    assertions = []
    assertions.extend(semantic_constraints)
    for condition in conditions or []:
        if condition is None:
            continue
        rendered_condition = self._render_auxiliary_smt(condition, parameters)
        if rendered_condition is None:
            return None
        assertions.append(f"(assert {rendered_condition})")
    left_smt = self._render_auxiliary_smt(left, parameters)
    right_smt = self._render_auxiliary_smt(right, parameters)
    if left_smt is None or right_smt is None:
        return None
    assertions.append(f"(assert (not (= {left_smt} {right_smt})))")
    return "\n".join(declarations + assertions + ["(check-sat)"])

def _impl__render_auxiliary_smt(
    self,
    node,
    symbol_specs: Sequence[Dict[str, Any]],
) -> Optional[str]:
    identity_to_spec = {
        spec.get("identity"): spec
        for spec in symbol_specs or []
        if spec.get("identity") is not None and spec.get("aux_name")
    }
    if isinstance(node, Condition):
        cloned_expr = self._clone_auxiliary_expression_for_smt(
            node.expression,
            identity_to_spec,
        )
        if cloned_expr is None:
            return None
        return Condition(cloned_expr, bool(getattr(node, "negated", False))).to_smt(float_mode="fp")
    if isinstance(node, Expression):
        cloned_expr = self._clone_auxiliary_expression_for_smt(
            node,
            identity_to_spec,
        )
        return cloned_expr.to_smt(float_mode="fp") if cloned_expr is not None else None
    return None

def _impl__auxiliary_smt_logic(
    self,
    expressions: Sequence[Optional[Expression]],
    conditions: Sequence[Condition],
) -> str:
    uses_float_theory = any(expression_uses_smt_float_theory(expr) for expr in expressions if expr is not None)
    uses_uf = any(expression_uses_smt_uf(expr, float_mode="fp") for expr in expressions if expr is not None)
    for condition in conditions or []:
        if condition is not None and expression_uses_smt_float_theory(condition.expression):
            uses_float_theory = True
        if condition is not None and expression_uses_smt_uf(condition.expression, float_mode="fp"):
            uses_uf = True
        if uses_float_theory and uses_uf:
            break
    return smt_logic_name(uses_float_theory=uses_float_theory, uses_uf=uses_uf)

def _impl__collect_auxiliary_float_declarations(
    self,
    expressions: Sequence[Optional[Expression]],
    conditions: Sequence[Condition],
) -> List[str]:
    declarations: List[str] = []
    for expr in expressions:
        for declaration in collect_float_predicate_smt_declarations(expr, float_mode="fp"):
            if declaration not in declarations:
                declarations.append(declaration)
    for condition in conditions or []:
        if condition is None:
            continue
        for declaration in collect_float_predicate_smt_declarations(condition.expression, float_mode="fp"):
            if declaration not in declarations:
                declarations.append(declaration)
    return declarations

def _impl__clone_auxiliary_expression_for_smt(
    self,
    expr: Optional[Expression],
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[Expression]:
    if expr is None:
        return None
    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.PARAMETER:
        identity = parameter_identity_key_from_expression(expr)
        if identity is None:
            return None
        symbol_spec = identity_to_spec.get(identity)
        if symbol_spec is None:
            return None
        aux_name = str(symbol_spec.get("aux_name") or "")
        if not aux_name:
            return None
        try:
            occurrence_size = max(1, int(getattr(expr, "size", 0) or 4))
            symbol_size = max(1, int(symbol_spec.get("size", 0) or occurrence_size))
        except (TypeError, ValueError):
            return None
        if occurrence_size > symbol_size:
            return None
        aux_expr = expr.clone_with(
            name=aux_name,
            value=int(symbol_spec.get("aux_index", -1) or -1),
            size=symbol_size,
        )
        if occurrence_size == symbol_size:
            return aux_expr
        return Expression(
            ExpressionType.BINARY_OP,
            operator="SUBPIECE",
            operands=[
                aux_expr,
                Expression.constant(0, size=8),
            ],
            size=occurrence_size,
        )
    if expr_type == ExpressionType.VARIABLE:
        return None
    if expr_type == ExpressionType.PHI:
        branches = []
        for condition, value in getattr(expr, "value", None) or []:
            cloned_condition = None
            if condition is not None:
                cloned_condition_expr = self._clone_auxiliary_expression_for_smt(
                    condition.expression,
                    identity_to_spec,
                )
                if cloned_condition_expr is None:
                    return None
                cloned_condition = Condition(
                    cloned_condition_expr,
                    bool(getattr(condition, "negated", False)),
                )
            cloned_value = self._clone_auxiliary_expression_for_smt(value, identity_to_spec)
            if cloned_value is None:
                return None
            branches.append((cloned_condition, cloned_value))
        return expr.clone_with(value=branches)
    operands = getattr(expr, "operands", None) or []
    if not operands:
        cloned_runtime_ref = self._clone_auxiliary_runtime_ref_for_smt(
            getattr(expr, "runtime_ref", None),
            identity_to_spec,
        )
        if cloned_runtime_ref is None and getattr(expr, "runtime_ref", None) is not None:
            return None
        return expr.clone_with(runtime_ref=cloned_runtime_ref) if cloned_runtime_ref is not None else expr
    cloned_operands = []
    for operand in operands:
        cloned_operand = self._clone_auxiliary_expression_for_smt(
            operand,
            identity_to_spec,
        )
        if cloned_operand is None:
            return None
        cloned_operands.append(cloned_operand)
    cloned_runtime_ref = self._clone_auxiliary_runtime_ref_for_smt(
        getattr(expr, "runtime_ref", None),
        identity_to_spec,
    )
    if cloned_runtime_ref is None and getattr(expr, "runtime_ref", None) is not None:
        return None
    if cloned_runtime_ref is not None:
        return expr.clone_with(operands=cloned_operands, runtime_ref=cloned_runtime_ref)
    return expr.clone_with(operands=cloned_operands)

def _impl__return_cases_have_smt_total_coverage(
    self,
    cases: Sequence[Any],
) -> Optional[bool]:
    miss_conditions: List[Condition] = []
    for case in cases or ():
        conditions = list(getattr(case, "conditions", None) or [])
        if not conditions:
            return True
        miss_expr = self._case_miss_expression(conditions)
        if miss_expr is None:
            return None
        miss_conditions.append(Condition(miss_expr, False))
    if not miss_conditions:
        return False

    parameters: List[Dict[str, Any]] = []
    for case in cases or ():
        parameters.extend(list(getattr(case, "parameters", None) or []))
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        miss_conditions,
        parameters,
    )
    return ConditionSMTOracle.conjunction_is_unsat(identity_conditions)

def _impl__try_solver_proven_rewrite_equivalence(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> QueryResult:
    return try_solver_proven_rewrite_equivalence(
        self,
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )

def _impl__solve_query_internal(
    self,
    query: str,
    pair_id: str,
    stage: str = "full",
    use_hard_timeout: bool = False
) -> QueryResult:
    return solve_query_internal(
        self,
        query,
        pair_id,
        stage=stage,
        use_hard_timeout=use_hard_timeout,
    )

def _impl__build_condition_only_query(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> str:
    return build_condition_only_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )

def _impl__save_unknown_query(self, query: str, pair_id: str, stage: str) -> None:
    save_unknown_query(self._debug_print, query, pair_id, stage, self.unknown_query_dir)

def _impl__build_single_case_condition_query(
    self,
    base_ctx: Dict[str, Any],
    case: ReturnCase,
    param_replace_fn,
    label: str,
) -> str:
    return build_single_case_condition_query(
        base_ctx,
        case,
        param_replace_fn,
        label,
    )

def _impl__build_pair_query(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> str:
    return build_pair_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )

def _impl__case_conditions_have_unsupported_smt_op_excluding_unknowns(self, case: ReturnCase) -> bool:
    for condition in getattr(case, "conditions", None) or ():
        expression = getattr(condition, "expression", None)
        if self._expression_has_unsupported_smt_op_excluding_unknowns(expression):
            return True
    return False

def _impl__expression_has_unsupported_smt_op_excluding_unknowns(self, expr: Any) -> bool:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return True
    if expr.expr_type == ExpressionType.UNKNOWN:
        return False
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for condition, value in expr.value:
            if condition is not None and self._expression_contains_unresolved(condition.expression):
                return True
            if self._expression_has_unsupported_smt_op_excluding_unknowns(value):
                return True
        return False
    if self._expression_node_is_unsupported_smt_op(expr):
        return True
    for operand in getattr(expr, "operands", []) or []:
        if self._expression_has_unsupported_smt_op_excluding_unknowns(operand):
            return True
    return False

def _impl__expression_node_is_unsupported_smt_op(self, expr: Any) -> bool:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return True
    if expr.expr_type == ExpressionType.UNKNOWN:
        return False
    return bool(expression_node_has_unsupported_smt_ops(expr))

def _impl__build_normalized_inequality_query(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    value1_norm_expr,
    value2_norm_expr,
    value1_smt_norm: str,
    value2_smt_norm: str,
    pair_id: str
) -> str:
    return build_normalized_inequality_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        value1_norm_expr,
        value2_norm_expr,
        value1_smt_norm,
        value2_smt_norm,
        pair_id,
    )

def _impl__pair_id_and_side_from_value_query_label(
    query_label: str,
) -> Tuple[Optional[str], Optional[str]]:
    if not isinstance(query_label, str) or ":" not in query_label:
        return None, None
    pair_id, suffix = query_label.rsplit(":", 1)
    if suffix == "value1":
        return pair_id, "left"
    if suffix == "value2":
        return pair_id, "right"
    return None, None
