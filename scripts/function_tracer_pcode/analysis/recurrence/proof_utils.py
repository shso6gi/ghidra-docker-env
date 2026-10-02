"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import collect_intrinsic_smt_declarations, collect_unknown_smt_declarations, expression_smt_bit_width
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.smt.parallel import run_backend_query
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ConditionSMTOracle,
    _expressions_equivalent_under_conditions,
    _runtime_expression_signature,
    canonicalize_location,
    coerce_value_to_bitvec_width,
)

class _PcodeExpressionTraversalState(Enum):
    ACTIVE = "ACTIVE"
    COMPLETED = "COMPLETED"
    UNAVAILABLE = "UNAVAILABLE"


@dataclass
class _PcodeExpressionTraversalContext:
    states: dict = field(default_factory=dict)
    expressions: dict = field(default_factory=dict)
    cycle_count: int = 0
    legacy_memo: Optional[dict] = None


def _pcode_expression_traversal_key(self, varnode, placeholders) -> tuple:
    placeholder_keys = tuple(sorted(
        repr(self._varnode_cache_key(candidate))
        for candidate in placeholders
    ))
    return (self._varnode_cache_key(varnode), placeholder_keys)


def _impl__implied_counter_constant_expression(
    self,
    conditions: Sequence[Condition],
    counter_expr: Expression,
    *,
    search_limit: int = 64,
) -> Optional[Expression]:
    if not conditions:
        return None
    size = max(1, int(getattr(counter_expr, "size", 0) or 4))
    for value in range(0, int(search_limit) + 1):
        diseq = Condition(
            Expression.binary_op(
                "INT_NOTEQUAL",
                counter_expr,
                Expression.constant(value, size=size),
            ),
            False,
        )
        proof_conditions = list(conditions) + [diseq]
        try:
            if ConditionSMTOracle.conjunction_is_unsat(proof_conditions) is True:
                return Expression.constant(value, size=size)
        except AnalysisLimitation:
            # Issue #106 PR-106-0: 解析の限界は「回復可能な失敗」ではない。ここで
            # 握り潰すと pair の打ち切りが遅れるので、そのまま上へ返す。
            raise
        except Exception:
            pass
        try:
            usable, script = ConditionSMTOracle._build_script(proof_conditions)
        except Exception:
            continue
        if not usable or not script:
            continue
        try:
            result = run_backend_query(Z3Solver(timeout=2, debug=False), script)
        except Exception:
            continue
        if result.status == SolverStatus.UNSAT:
            return Expression.constant(value, size=size)
    return None

def _impl__expression_prefers_signed_extension(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    data_type = str(getattr(expr, "data_type", "") or "").lower()
    if "unsigned" in data_type or data_type.startswith("u"):
        return False
    if any(token in data_type for token in ("signed", "int", "long", "short", "char")):
        return True
    return False

def _impl__coerce_summary_expression_to_size(
    self,
    expr: Expression,
    target_size: int,
    *,
    signed: bool = False,
) -> Expression:
    target_size = max(1, int(target_size or 0))
    expr_size = int(getattr(expr, "size", 0) or 0)
    if expr_size <= 0:
        expr_size = target_size
    if expr_size == target_size:
        return expr
    if expr_size > target_size:
        narrowed = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, size=4))
        narrowed.size = target_size
        return narrowed
    widened = Expression.unary_op("INT_SEXT" if signed else "INT_ZEXT", expr)
    widened.size = target_size
    return widened

def _impl__expression_integer_constants(self, expr: Optional[Expression]) -> List[int]:
    values: List[int] = []
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.CONSTANT:
            continue
        value = self._raw_constant_value(node)
        if value is not None:
            values.append(int(value))
    return values

def _impl__normalize_counter_parameter_expression(
    self,
    expr: Optional[Expression],
    counter_param: dict,
    counter_expr: Expression,
) -> Optional[Expression]:
    if expr is None:
        return None
    normalized = expr
    for candidate in self._parameter_expression_candidates(
        counter_param,
        (expr,),
        include_primary=False,
        primary=counter_expr,
    ):
        if not self._counter_parameter_candidate_can_normalize(
            candidate,
            counter_param,
            counter_expr,
        ):
            continue
        substituted = self._substitute_exact_expression(normalized, candidate, counter_expr)
        if substituted is not None:
            normalized = substituted
    return normalized

def _impl__parameter_expression_candidates(
    self,
    parameter: dict,
    expressions: Sequence[Optional[Expression]],
    *,
    include_primary: bool = True,
    primary: Optional[Expression] = None,
) -> Tuple[Expression, ...]:
    primary = primary or self._parameter_expression(parameter)
    candidates: List[Expression] = []

    def add(expr: Expression) -> None:
        if expr is None:
            return
        if any(
            existing.equals(expr)
            and getattr(existing, "data_type", None) == getattr(expr, "data_type", None)
            and getattr(existing, "data_type_obj", None) is getattr(expr, "data_type_obj", None)
            for existing in candidates
        ):
            return
        candidates.append(expr)

    expected_name = parameter.get("name")
    try:
        expected_index = int(parameter.get("index")) if parameter.get("index") is not None else -1
    except (TypeError, ValueError):
        expected_index = -1
    expected_size = int(parameter.get("size") or getattr(primary, "size", 0) or 0)
    expected_storage = getattr(primary, "storage_info", None)
    for expr in expressions or ():
        for node in self._iter_expression_nodes(expr):
            if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
                continue
            try:
                node_index = int(getattr(node, "value", -1))
            except (TypeError, ValueError):
                node_index = -1
            same_index = expected_index >= 0 and node_index == expected_index
            same_name = expected_name is not None and getattr(node, "name", None) == expected_name
            same_storage = (
                expected_storage is not None
                and getattr(node, "storage_info", None) is not None
                and getattr(node, "storage_info", None) == expected_storage
            )
            same_size = expected_size <= 0 or int(getattr(node, "size", 0) or 0) == expected_size
            if same_size and (same_index or same_name or same_storage):
                add(node)
    if include_primary:
        add(primary)
    return tuple(candidates)

def _impl__expression_depends_on_signature(
    self,
    expr: Optional[Expression],
    target_signature,
) -> bool:
    if expr is None:
        return False
    if _runtime_expression_signature(expr) == target_signature:
        return True
    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.PHI:
        for cond, branch_value in getattr(expr, "value", None) or []:
            if cond is not None and self._expression_depends_on_signature(getattr(cond, "expression", None), target_signature):
                return True
            if self._expression_depends_on_signature(branch_value, target_signature):
                return True
        return False
    for operand in getattr(expr, "operands", None) or []:
        if self._expression_depends_on_signature(operand, target_signature):
            return True
    return False

def _impl__collect_expression_symbol_specs(
    self,
    *exprs: Optional[Expression],
) -> Optional[List[dict]]:
    specs: Dict[Tuple[Any, ...], dict] = {}
    unresolved_symbol = False

    def add_symbol(identity: Optional[Tuple[Any, ...]], candidate: dict) -> None:
        if identity is None:
            return
        size = max(1, int(candidate.get("size", 0) or 4))
        candidate = {
            **candidate,
            "identity": identity,
            "size": size,
        }
        existing = specs.get(identity)
        if existing is None or int(existing.get("size", 0) or 0) < size:
            specs[identity] = candidate

    def visit(expr: Optional[Expression]) -> None:
        nonlocal unresolved_symbol
        if expr is None:
            return
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PARAMETER:
            identity = self._summary_symbol_identity_from_expression(expr)
            if identity is None:
                unresolved_symbol = True
                return
            add_symbol(identity, self._summary_symbol_spec_from_expression(expr))
            return
        if expr_type == ExpressionType.VARIABLE:
            identity = self._summary_symbol_identity_from_expression(expr)
            if identity is None:
                unresolved_symbol = True
                return
            add_symbol(identity, self._summary_symbol_spec_from_expression(expr))
            return
        if expr_type == ExpressionType.PHI:
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
            self._summary_symbol_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    )
    for ordinal, spec in enumerate(ordered):
        spec["aux_name"] = f"aux_sym_{ordinal}"
        spec["aux_index"] = ordinal
    return ordered

def _impl__summary_symbol_spec_from_expression(
    self,
    expr: Expression,
) -> dict:
    result = {
        "name": str(getattr(expr, "name", None) or ""),
        "index": int(getattr(expr, "value", -1) or -1),
        "size": max(1, int(getattr(expr, "size", 0) or 4)),
        "data_type": getattr(expr, "data_type", None),
        "is_signed": bool(getattr(expr, "is_signed", True)),
    }
    storage_info = getattr(expr, "storage_info", None)
    if storage_info is not None:
        result["storage_info"] = storage_info
    return result

def _impl__build_expression_equivalence_query(
    self,
    left: Expression,
    right: Expression,
    conditions: Sequence[Condition],
    parameters: Optional[Sequence[dict]],
) -> Optional[str]:
    if left is None or right is None:
        return None
    memory_widths = self._collect_expression_memory_widths(
        left,
        right,
        *(condition.expression for condition in conditions or [] if condition is not None),
    )
    declarations = ["(set-logic QF_AUFBV)" if memory_widths else "(set-logic QF_BV)"]

    expression_symbols = self._collect_expression_symbol_specs(
        left,
        right,
        *(condition.expression for condition in conditions or [] if condition is not None),
    )
    if expression_symbols is None:
        return None
    symbol_specs: Dict[Tuple[Any, ...], dict] = {
        item.get("identity"): dict(item)
        for item in expression_symbols
        if item.get("identity") is not None
    }
    for parameter in parameters or []:
        identity = self._summary_symbol_identity_from_descriptor(dict(parameter))
        if identity is None:
            continue
        candidate = dict(parameter)
        candidate["identity"] = identity
        candidate["size"] = max(1, int(candidate.get("size", 0) or 4))
        existing = symbol_specs.get(identity)
        if existing is None or int(existing.get("size", 0) or 0) < int(parameter.get("size", 0) or 0):
            symbol_specs[identity] = candidate
    ordered_symbol_specs = self._assign_summary_auxiliary_symbols(symbol_specs.values())

    symbol_infos = self._build_auxiliary_parameter_infos(
        ordered_symbol_specs,
    )
    for symbol in symbol_infos:
        declarations.append(f"(declare-const {symbol.smt_name} (_ BitVec {symbol.bit_width}))")
    for mem_bits in sorted(memory_widths):
        declarations.append(
            f"(declare-const mem{mem_bits} (Array (_ BitVec 64) (_ BitVec {mem_bits})))"
        )
    seen_unknown_decls = set()
    for expr in (left, right):
        for decl in collect_unknown_smt_declarations(expr):
            if decl in seen_unknown_decls:
                continue
            seen_unknown_decls.add(decl)
            declarations.append(f"(declare-const {decl[0]} (_ BitVec {decl[1]}))")
    for condition in conditions or []:
        if condition is None:
            continue
        for decl in collect_unknown_smt_declarations(condition.expression):
            if decl in seen_unknown_decls:
                continue
            seen_unknown_decls.add(decl)
            declarations.append(f"(declare-const {decl[0]} (_ BitVec {decl[1]}))")
    intrinsic_declarations: List[str] = []
    for expr in (left, right):
        for declaration in collect_intrinsic_smt_declarations(expr):
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
    for condition in conditions or []:
        if condition is None:
            continue
        for declaration in collect_intrinsic_smt_declarations(condition.expression):
            if declaration not in intrinsic_declarations:
                intrinsic_declarations.append(declaration)
    declarations.extend(intrinsic_declarations)

    assertions = []
    for condition in conditions or []:
        if condition is None:
            continue
        rendered_condition = self._render_summary_auxiliary_smt(condition, ordered_symbol_specs)
        if rendered_condition is None:
            return None
        assertions.append(f"(assert {rendered_condition})")
    target_bits = max(1, self._expression_equivalence_target_bits(left, right))
    left_rendered = self._render_summary_auxiliary_smt(left, ordered_symbol_specs)
    right_rendered = self._render_summary_auxiliary_smt(right, ordered_symbol_specs)
    if left_rendered is None or right_rendered is None:
        return None
    left_smt = coerce_value_to_bitvec_width(
        left,
        left_rendered,
        target_bits,
        use_sign_extension=False,
    )
    right_smt = coerce_value_to_bitvec_width(
        right,
        right_rendered,
        target_bits,
        use_sign_extension=False,
    )
    assertions.append(f"(assert (not (= {left_smt} {right_smt})))")
    return "\n".join(declarations + assertions + ["(check-sat)"])

def _impl__collect_expression_memory_widths(
    self,
    *exprs: Optional[Expression],
) -> List[int]:
    widths: set[int] = set()

    def visit(expr: Optional[Expression]) -> None:
        if expr is None:
            return
        if getattr(expr, "expr_type", None) == ExpressionType.MEMORY:
            bits = max(1, int(expression_smt_bit_width(expr) or 0))
            if bits in {8, 16, 32, 64}:
                widths.add(bits)
        for operand in getattr(expr, "operands", None) or []:
            visit(operand)
        if getattr(expr, "expr_type", None) == ExpressionType.PHI:
            for cond, branch_value in getattr(expr, "value", None) or []:
                if cond is not None:
                    visit(getattr(cond, "expression", None))
                visit(branch_value)

    for expr in exprs:
        visit(expr)
    return sorted(widths)

def _impl__expression_equivalence_target_bits(
    self,
    left: Expression,
    right: Expression,
) -> int:
    left_bits = int(getattr(left, "get_bit_width", lambda: 0)() or 0)
    right_bits = int(getattr(right, "get_bit_width", lambda: 0)() or 0)
    try:
        from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width

        left_bits = max(left_bits, int(expression_smt_bit_width(left) or 0))
        right_bits = max(right_bits, int(expression_smt_bit_width(right) or 0))
    except Exception:
        pass
    return max(left_bits, right_bits, 32)

def _impl__render_summary_auxiliary_smt(
    self,
    node,
    symbol_specs: Sequence[dict],
) -> Optional[str]:
    from scripts.function_tracer_pcode.core.render_smt import UnsupportedSmtSemanticsError

    identity_to_spec = {
        spec.get("identity"): spec
        for spec in symbol_specs or []
        if spec.get("identity") is not None and spec.get("aux_name")
    }
    try:
        if isinstance(node, Condition):
            cloned_expr = self._clone_summary_expression_for_smt(node.expression, identity_to_spec)
            if cloned_expr is None:
                return None
            # 差し替えの組み立て完了点。以後手は入らない。
            # 条件も 1 つの意味値。式だけ公開しても、包んだ条件は別 object
            # なので producer が宣言し直す必要がある。
            return publish(
                Condition(cloned_expr, bool(getattr(node, "negated", False)))
            ).to_smt()
        if isinstance(node, Expression):
            cloned_expr = self._clone_summary_expression_for_smt(node, identity_to_spec)
            if cloned_expr is None:
                return None
            publish(cloned_expr)
            return cloned_expr.to_smt()
    except UnsupportedSmtSemanticsError:
        # Auxiliary recurrence proofs are optional promotion evidence.  An
        # expression without an exact SMT lowering must reject that proof
        # attempt conservatively instead of aborting the whole analysis.
        return None
    return None

def _impl__clone_summary_expression_for_smt(
    self,
    expr: Optional[Expression],
    identity_to_spec: Dict[Tuple[Any, ...], dict],
) -> Optional[Expression]:
    if expr is None:
        return None
    expr_type = getattr(expr, "expr_type", None)
    if expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        identity = self._summary_symbol_identity_from_expression(expr)
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
        aux_expr = Expression.parameter(
            aux_name,
            index=int(symbol_spec.get("aux_index", -1) or -1),
            data_type=getattr(expr, "data_type", None),
            data_type_obj=getattr(expr, "data_type_obj", None),
            size=symbol_size,
            storage_info=getattr(expr, "storage_info", None),
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
    if expr_type == ExpressionType.PHI:
        branches = []
        for condition, value in getattr(expr, "value", None) or []:
            cloned_condition = None
            if condition is not None:
                cloned_condition_expr = self._clone_summary_expression_for_smt(
                    condition.expression,
                    identity_to_spec,
                )
                if cloned_condition_expr is None:
                    return None
                cloned_condition = Condition(
                    cloned_condition_expr,
                    bool(getattr(condition, "negated", False)),
                )
            cloned_value = self._clone_summary_expression_for_smt(value, identity_to_spec)
            if cloned_value is None:
                return None
            branches.append((cloned_condition, cloned_value))
        return expr.clone_with(value=branches)
    operands = getattr(expr, "operands", None) or []
    if not operands:
        return expr
    cloned_operands = []
    for operand in operands:
        cloned_operand = self._clone_summary_expression_for_smt(operand, identity_to_spec)
        if cloned_operand is None:
            return None
        cloned_operands.append(cloned_operand)
    return expr.clone_with(operands=cloned_operands)

def _impl__build_pcode_expression(
    self,
    varnode,
    *,
    placeholders: Dict[object, Expression],
    _seen=None,
    _memo=None,
) -> Optional[Expression]:
    if varnode is None:
        return None
    return _build_pcode_expression_with_context(
        self,
        varnode,
        placeholders=placeholders,
        context=_PcodeExpressionTraversalContext(legacy_memo=_memo),
    )


def _build_pcode_expression_with_context(
    self,
    varnode,
    *,
    placeholders: Dict[object, Expression],
    context: _PcodeExpressionTraversalContext,
) -> Optional[Expression]:
    if varnode is None:
        return None
    key = _pcode_expression_traversal_key(self, varnode, placeholders)
    state = context.states.get(key)
    if state is _PcodeExpressionTraversalState.ACTIVE:
        context.cycle_count += 1
        return None
    if state is _PcodeExpressionTraversalState.UNAVAILABLE:
        return None
    if state is _PcodeExpressionTraversalState.COMPLETED:
        return context.expressions[key]
    if context.legacy_memo is not None:
        cached = context.legacy_memo.get(key)
        if cached is False:
            context.states[key] = _PcodeExpressionTraversalState.UNAVAILABLE
            return None
        if cached is not None:
            context.states[key] = _PcodeExpressionTraversalState.COMPLETED
            context.expressions[key] = cached
            return cached

    context.states[key] = _PcodeExpressionTraversalState.ACTIVE
    cycle_count = context.cycle_count
    try:
        result = _build_pcode_expression_active(
            self,
            varnode,
            placeholders=placeholders,
            context=context,
        )
    except Exception:
        context.states[key] = _PcodeExpressionTraversalState.UNAVAILABLE
        if context.legacy_memo is not None:
            context.legacy_memo[key] = False
        raise
    if context.cycle_count != cycle_count:
        result = None
    if result is None:
        context.states[key] = _PcodeExpressionTraversalState.UNAVAILABLE
        if context.legacy_memo is not None:
            context.legacy_memo[key] = False
        return None
    context.states[key] = _PcodeExpressionTraversalState.COMPLETED
    context.expressions[key] = result
    if context.legacy_memo is not None:
        context.legacy_memo[key] = result
    return result


def _build_pcode_expression_active(
    self,
    varnode,
    *,
    placeholders: Dict[object, Expression],
    context: _PcodeExpressionTraversalContext,
) -> Optional[Expression]:
    for candidate, replacement in placeholders.items():
        if self._same_placeholder_varnode(varnode, candidate):
            return replacement

    current = self._follow_passthrough_varnode(varnode)
    if current is not varnode:
        current_key = _pcode_expression_traversal_key(
            self, current, placeholders
        )
        varnode_key = _pcode_expression_traversal_key(
            self, varnode, placeholders
        )
        if current_key != varnode_key:
            return _build_pcode_expression_with_context(
                self,
                current,
                placeholders=placeholders,
                context=context,
            )
    for candidate, replacement in placeholders.items():
        if self._same_placeholder_varnode(current, candidate):
            return replacement

    def_op = getattr(current, "getDef", lambda: None)()
    if def_op is None:
        traced = self._trace_varnode_expression(current)
        if traced is None or self._expression_is_unresolved(traced):
            return None
        return traced

    mnemonic = getattr(def_op, "getMnemonic", lambda: None)()
    output = getattr(def_op, "getOutput", lambda: None)()
    output_size = max(1, int(getattr(output, "getSize", lambda: 0)() or getattr(current, "getSize", lambda: 0)() or 1))

    if mnemonic == "MULTIEQUAL":
        parent_block = getattr(def_op, "getParent", lambda: None)()
        input_count = int(getattr(def_op, "getNumInputs", lambda: 0)() or 0)
        branches = []
        for index in range(input_count):
            value = _build_pcode_expression_with_context(
                self,
                def_op.getInput(index),
                placeholders=placeholders,
                context=context,
            )
            if value is None:
                continue
            condition = None
            if parent_block is not None and index < int(getattr(parent_block, "getInSize", lambda: 0)() or 0):
                predecessor = parent_block.getIn(index)
                condition = _build_block_edge_condition_with_context(
                    self,
                    predecessor,
                    parent_block,
                    placeholders=placeholders,
                    context=context,
                )
            branches.append((condition, value))
        if not branches:
            return None
        if len(branches) == 1 and branches[0][0] is None:
            return branches[0][1]
        phi = Expression.phi(branches)
        phi.size = output_size
        return phi

    if mnemonic in {"COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE"}:
        expr = _build_pcode_expression_with_context(
            self,
            def_op.getInput(0),
            placeholders=placeholders,
            context=context,
        )
        if expr is None:
            return None
        if mnemonic in {"COPY", "CAST"}:
            expr.size = output_size
            return expr
        if mnemonic in {"INT_ZEXT", "INT_SEXT"}:
            widened = Expression.unary_op(mnemonic, expr)
            widened.size = output_size
            return widened
        if mnemonic == "SUBPIECE":
            if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) < 2:
                return None
            offset_expr = _build_pcode_expression_with_context(
                self,
                def_op.getInput(1),
                placeholders=placeholders,
                context=context,
            )
            if offset_expr is None:
                return None
            subpiece = Expression.binary_op("SUBPIECE", expr, offset_expr)
            subpiece.size = output_size
            return subpiece

    if mnemonic in {"INT_NEGATE", "INT_2COMP", "BOOL_NEGATE"}:
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) != 1:
            return None
        operand = _build_pcode_expression_with_context(
            self,
            def_op.getInput(0),
            placeholders=placeholders,
            context=context,
        )
        if operand is None:
            return None
        unary = Expression.unary_op(mnemonic, operand)
        unary.size = output_size
        return unary

    if mnemonic in {
        "INT_ADD",
        "INT_SUB",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "PIECE",
        "INT_LEFT",
        "INT_RIGHT",
        "INT_SRIGHT",
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_LESSEQUAL",
        "INT_SLESS",
        "INT_SLESSEQUAL",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
    }:
        if int(getattr(def_op, "getNumInputs", lambda: 0)() or 0) != 2:
            return None
        left = _build_pcode_expression_with_context(
            self,
            def_op.getInput(0),
            placeholders=placeholders,
            context=context,
        )
        right = _build_pcode_expression_with_context(
            self,
            def_op.getInput(1),
            placeholders=placeholders,
            context=context,
        )
        if left is None or right is None:
            return None
        expr = Expression.binary_op(mnemonic, left, right)
        expr.size = output_size
        return expr

    return None


def _build_block_edge_condition_with_context(
    self,
    block,
    successor,
    *,
    placeholders: Dict[object, Expression],
    context: _PcodeExpressionTraversalContext,
) -> Optional[Condition]:
    cbranch = self._find_cbranch_op(block)
    if cbranch is None or int(
        getattr(cbranch, "getNumInputs", lambda: 0)() or 0
    ) < 2:
        return None
    expr = _build_pcode_expression_with_context(
        self,
        cbranch.getInput(1),
        placeholders=placeholders,
        context=context,
    )
    if expr is None or self._expression_is_unresolved(expr):
        return None

    true_out = getattr(block, "getTrueOut", lambda: None)()
    false_out = getattr(block, "getFalseOut", lambda: None)()
    successor_key = self._block_key(successor)
    if true_out is not None and self._block_key(true_out) == successor_key:
        return Condition(expr, False)
    if false_out is not None and self._block_key(false_out) == successor_key:
        return Condition(expr, True)
    return None


def _impl__copy_symbol_expression(self, expr: Expression, size: int) -> Expression:
    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        return Expression.parameter(
            getattr(expr, "name", None) or "param",
            index=int(getattr(expr, "value", -1) or -1),
            data_type=getattr(expr, "data_type", None),
            data_type_obj=getattr(expr, "data_type_obj", None),
            size=max(1, int(size or getattr(expr, "size", 0) or 4)),
            storage_info=getattr(expr, "storage_info", None),
            runtime_ref=getattr(expr, "runtime_ref", None),
        )
    if getattr(expr, "expr_type", None) == ExpressionType.VARIABLE:
        return Expression.variable(
            getattr(expr, "name", None) or "var",
            data_type=getattr(expr, "data_type", None),
            data_type_obj=getattr(expr, "data_type_obj", None),
            size=max(1, int(size or getattr(expr, "size", 0) or 4)),
            storage_info=getattr(expr, "storage_info", None),
            runtime_ref=getattr(expr, "runtime_ref", None),
        )
    return expr

def _impl__expression_is_unresolved(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return True
    if expr.expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and self._expression_is_unresolved(cond.expression):
                return True
            if self._expression_is_unresolved(value):
                return True
        return False
    return any(self._expression_is_unresolved(operand) for operand in getattr(expr, "operands", []) or [])

def _impl__expression_is_loop_invariant_bias(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    expr_type = getattr(expr, "expr_type", None)
    if expr_type in {ExpressionType.CONSTANT, ExpressionType.PARAMETER}:
        return True
    runtime_ref = getattr(expr, "runtime_ref", None)
    if runtime_ref is not None and not (
        bool(getattr(runtime_ref, "loop_invariant", False))
        or bool(getattr(runtime_ref, "is_loop_invariant", False))
    ):
        return False
    if expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL, ExpressionType.VARIABLE, ExpressionType.PHI}:
        return False
    operands = tuple(getattr(expr, "operands", ()) or ())
    if not operands:
        return False
    return all(self._expression_is_loop_invariant_bias(operand) for operand in operands)

def _impl__substitute_exact_expression(
    self,
    expr: Optional[Expression],
    needle: Expression,
    replacement: Expression,
) -> Optional[Expression]:
    if expr is None:
        return None
    if expr.structural_key() == needle.structural_key():
        return replacement

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = self._substitute_exact_expression(expr.operands[0], needle, replacement)
        right = self._substitute_exact_expression(expr.operands[1], needle, replacement)
        if left is expr.operands[0] and right is expr.operands[1]:
            return expr
        rebuilt = Expression.binary_op(expr.operator, left, right)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
        operand = self._substitute_exact_expression(expr.operands[0], needle, replacement)
        if operand is expr.operands[0]:
            return expr
        rebuilt = Expression.unary_op(expr.operator, operand)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for condition, value in expr.value:
            new_condition = condition
            if condition is not None:
                condition_expr = self._substitute_exact_expression(
                    condition.expression,
                    needle,
                    replacement,
                )
                if condition_expr is not condition.expression:
                    new_condition = Condition(condition_expr, condition.negated)
                    changed = True
            new_value = self._substitute_exact_expression(value, needle, replacement)
            if new_value is not value:
                changed = True
            branches.append((new_condition, new_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY} and expr.operands:
        new_operands = [
            self._substitute_exact_expression(operand, needle, replacement)
            for operand in expr.operands
        ]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return expr
        if expr.expr_type == ExpressionType.CALL:
            rebuilt = Expression.call(expr.name or "call", new_operands)
        elif expr.expr_type == ExpressionType.INTRINSIC:
            rebuilt = Expression.intrinsic(
                expr.name or "intrinsic",
                new_operands,
                size=expr.size,
                runtime_ref=expr.runtime_ref,
                opcode=expr.opcode,
            )
        else:
            rebuilt = Expression.memory(
                new_operands[0],
                size=expr.size,
                read_order_key=expr.read_order_key,
                runtime_ref=expr.runtime_ref,
            )
        rebuilt.size = expr.size
        return rebuilt

    return expr

def _impl__flatten_bool_and_expression(self, expr: Optional[Expression]) -> Tuple[Expression, ...]:
    if expr is None:
        return ()
    expr = self._canonicalize_expression(expr)
    if (
        expr.expr_type == ExpressionType.BINARY_OP
        and expr.operator == "BOOL_AND"
        and len(expr.operands) == 2
    ):
        return self._flatten_bool_and_expression(expr.operands[0]) + self._flatten_bool_and_expression(expr.operands[1])
    return (expr,)

def _impl__expression_contains_subexpression(
    self,
    expr: Optional[Expression],
    needle: Optional[Expression],
) -> bool:
    if expr is None or needle is None:
        return False
    try:
        needle_key = needle.structural_key()
    except (AttributeError, TypeError, ValueError, RecursionError):
        return False
    for node in self._iter_expression_nodes(expr):
        try:
            if node.structural_key() == needle_key:
                return True
        except (AttributeError, TypeError, ValueError, RecursionError):
            continue
    return False

def _impl__expression_mentions_placeholder(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
) -> bool:
    placeholder_key = placeholder.structural_key()
    for node in self._iter_expression_nodes(expr):
        try:
            if node.structural_key() == placeholder_key:
                return True
        except (AttributeError, TypeError, ValueError, RecursionError):
            continue
    return False

def _impl__iter_expression_nodes(self, expr: Optional[Expression]):
    if expr is None:
        return
    stack = [expr]
    seen = set()
    while stack:
        current = stack.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        yield current
        if current.expr_type == ExpressionType.PHI and current.value:
            for cond, value in current.value:
                if cond is not None and getattr(cond, "expression", None) is not None:
                    stack.append(cond.expression)
                if value is not None:
                    stack.append(value)
            continue
        for operand in reversed(list(getattr(current, "operands", None) or [])):
            stack.append(operand)

def _impl__expression_tree_contains_type(
    self,
    expr: Optional[Expression],
    expr_type: ExpressionType,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == expr_type:
        return True
    if expr.expr_type == ExpressionType.PHI and expr.value:
        return any(
            (condition is not None and self._expression_tree_contains_type(condition.expression, expr_type))
            or self._expression_tree_contains_type(value, expr_type)
            for condition, value in expr.value
        )
    return any(
        self._expression_tree_contains_type(operand, expr_type)
        for operand in (expr.operands or [])
    )

def _impl__loop_variable_expression(
    self,
    scope: Optional[Dict[Tuple[str, Tuple[Any, ...]], int]],
    role: str,
    name: str,
    varnode,
    size: object,
) -> Expression:
    try:
        normalized_size = max(1, int(size or 4))
    except (TypeError, ValueError):
        normalized_size = 4
    return Expression.variable(
        name,
        size=normalized_size,
        runtime_ref=self._loop_variable_identity_ref(
            role,
            varnode,
            binder_ordinal=self._loop_variable_binder_ordinal(scope, role, varnode),
        ),
    )

def _impl__trace_varnode_expression(
    self,
    varnode,
) -> Optional[Expression]:
    if varnode is None:
        return None
    try:
        return self.tracer.trace_varnode(varnode, 0, use_cache=False)
    except TypeError:
        try:
            return self.tracer.trace_varnode(varnode, use_cache=False)
        except Exception:
            return None
    except Exception:
        return None

def _impl__terms_equivalent(
    self,
    left: Expression,
    right: Expression,
    parameters: Sequence[dict],
) -> bool:
    if _expressions_equivalent_under_conditions(left, right, [], parameters):
        return True
    if (
        left.expr_type == ExpressionType.MEMORY
        and right.expr_type == ExpressionType.MEMORY
        and left.operands
        and right.operands
    ):
        left_loc = canonicalize_location(left.operands[0], parameters, size=left.size)
        right_loc = canonicalize_location(right.operands[0], parameters, size=right.size)
        if left_loc is not None and right_loc is not None:
            return left_loc == right_loc
    return _runtime_expression_signature(left) == _runtime_expression_signature(right)

def _impl__scale_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
    if factor == 0:
        return None
    if factor == 1:
        return expr
    if factor == -1:
        negated = Expression.unary_op("INT_2COMP", expr)
        negated.size = expr.size
        return negated
    return Expression.binary_op(
        "INT_MULT",
        Expression.constant(factor, size=expr.size or 4),
        expr,
    )

def _impl__sum_expression_terms(
    self,
    terms: Sequence[Optional[Expression]],
) -> Optional[Expression]:
    normalized = [term for term in terms if term is not None]
    if not normalized:
        return Expression.constant(0, 4)
    total = normalized[0]
    for term in normalized[1:]:
        total = Expression.binary_op("INT_ADD", total, term)
        total.size = max(total.size, term.size)
    return total

def _impl__parameter_expression(self, param_info: dict) -> Expression:
    size = int(param_info.get("size") or 4)
    storage_info = self._summary_storage_info_from_parameter(param_info)
    try:
        index = int(param_info.get("index")) if param_info.get("index") is not None else -1
    except (TypeError, ValueError):
        index = -1
    return Expression.parameter(
        param_info.get("name", "param_1"),
        index=index,
        data_type=param_info.get("data_type"),
        data_type_obj=param_info.get("data_type_obj"),
        size=size,
        storage_info=storage_info,
    )

def _impl__is_constant_expression(self, expr: Optional[Expression]) -> bool:
    return expr is not None and expr.expr_type == ExpressionType.CONSTANT

def _impl__extract_addend_expression(self, expr: Expression, function_name: str) -> Optional[Expression]:
    if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    if expr.operator not in {"INT_ADD", "INT_SUB"}:
        return None

    left, right = expr.operands
    if self._expression_contains_recursive_unknown(left, function_name) and not self._expression_contains_recursive_unknown(right, function_name):
        if expr.operator == "INT_ADD":
            return right
        if expr.operator == "INT_SUB":
            return Expression.unary_op("INT_2COMP", right)
    if self._expression_contains_recursive_unknown(right, function_name) and not self._expression_contains_recursive_unknown(left, function_name):
        if expr.operator == "INT_ADD":
            return left
    return None
