"""Budgeted minimal-satisfying-extension frontier evaluator."""

from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, Iterable, Mapping, MutableMapping, Set, Tuple

from .contracts import (
    BoundSatisfactionContract,
    ExpressionKind,
    SatisfactionContractDefinition,
    SatisfactionExpression,
)


class FrontierBudgetExceeded(RuntimeError):
    """No authoritative frontier exists when this exception is raised."""


@dataclass(frozen=True)
class FrontierEvaluationBudget:
    max_expression_nodes: int = 256
    max_antichain_sets: int = 1024
    max_requirement_ids: int = 256
    max_union_operations: int = 4096

    def __post_init__(self) -> None:
        if min(
            self.max_expression_nodes,
            self.max_antichain_sets,
            self.max_requirement_ids,
            self.max_union_operations,
        ) < 1:
            raise ValueError("frontier budget values must be positive")


@dataclass(frozen=True)
class FrontierEvaluation:
    minimal_satisfying_extensions: Tuple[FrozenSet[str], ...]
    live_open_requirements: FrozenSet[str]
    satisfied: bool
    expression_nodes: int
    antichain_sets: int
    requirement_ids: int
    union_operations: int


@dataclass
class _Usage:
    nodes: int = 0
    sets: int = 0
    unions: int = 0


def evaluate_live_frontier(
    definition: SatisfactionContractDefinition,
    bound: BoundSatisfactionContract,
    completed_requirement_ids: Iterable[str],
    budget: FrontierEvaluationBudget = FrontierEvaluationBudget(),
) -> FrontierEvaluation:
    bound.validate_against(definition)
    bindings = {
        name: requirement.requirement_id for name, requirement in bound.slot_bindings
    }
    declared = frozenset(bindings.values())
    if len(declared) > budget.max_requirement_ids:
        raise FrontierBudgetExceeded("requirement-id budget exceeded")
    completed = frozenset(completed_requirement_ids)
    if not completed.issubset(declared):
        raise ValueError("completion set contains an undeclared proof requirement")
    usage = _Usage()
    antichain = _evaluate(
        definition.normalized_expression_template,
        bindings,
        completed,
        budget,
        usage,
    )
    ordered = tuple(sorted(antichain, key=lambda item: (len(item), tuple(sorted(item)))))
    live = frozenset(requirement for extension in ordered for requirement in extension)
    return FrontierEvaluation(
        minimal_satisfying_extensions=ordered,
        live_open_requirements=live,
        satisfied=frozenset() in antichain,
        expression_nodes=usage.nodes,
        antichain_sets=usage.sets,
        requirement_ids=len(declared),
        union_operations=usage.unions,
    )


def _evaluate(
    expression: SatisfactionExpression,
    bindings: Mapping[str, str],
    completed: FrozenSet[str],
    budget: FrontierEvaluationBudget,
    usage: _Usage,
) -> Set[FrozenSet[str]]:
    usage.nodes += 1
    _check_usage(usage, budget)
    if expression.kind == ExpressionKind.REQUIREMENT_SLOT:
        requirement_id = bindings[str(expression.slot_name)]
        result = {frozenset()} if requirement_id in completed else {frozenset((requirement_id,))}
        usage.sets += len(result)
        _check_usage(usage, budget)
        return result
    children = [
        _evaluate(child, bindings, completed, budget, usage)
        for child in expression.children
    ]
    if expression.kind == ExpressionKind.ANY_OF:
        candidates = set().union(*children)
        result = _minimal(candidates)
        usage.sets += len(result)
        _check_usage(usage, budget)
        return result
    product: Set[FrozenSet[str]] = {frozenset()}
    for child_sets in children:
        next_product = set()
        for left in product:
            for right in child_sets:
                usage.unions += 1
                _check_usage(usage, budget)
                next_product.add(left.union(right))
        product = _minimal(next_product)
        usage.sets += len(product)
        _check_usage(usage, budget)
    return product


def _minimal(candidates: Iterable[FrozenSet[str]]) -> Set[FrozenSet[str]]:
    ordered = sorted(set(candidates), key=lambda item: (len(item), tuple(sorted(item))))
    result: Set[FrozenSet[str]] = set()
    for candidate in ordered:
        if not any(existing.issubset(candidate) for existing in result):
            result.add(candidate)
    return result


def _check_usage(usage: _Usage, budget: FrontierEvaluationBudget) -> None:
    if usage.nodes > budget.max_expression_nodes:
        raise FrontierBudgetExceeded("expression-node budget exceeded")
    if usage.sets > budget.max_antichain_sets:
        raise FrontierBudgetExceeded("antichain-set budget exceeded")
    if usage.unions > budget.max_union_operations:
        raise FrontierBudgetExceeded("union-operation budget exceeded")
