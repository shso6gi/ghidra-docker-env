# -*- coding: utf-8 -*-
"""Concrete-execution evaluation: a baseline tree against a treatment tree (Issue #323, C4).

Usage::

    python3 -B -m scripts.function_tracer_pcode.reporting.concrete_evaluation \\
        --baseline <tree run with EQBENCH_CONCRETE_STAGES=none> \\
        --treatment <tree run with EQBENCH_CONCRETE_STAGES=witness_replay> \\
        [--json report.json] [--pairs pairs.tsv] [--allow-difference NAME ...]

The two trees are meant to differ in the concrete-execution setting only: same
source, same analysis config apart from the concrete fields, same pairs, same
binaries.  The report first checks that (``conditions``); a difference it finds
makes the comparison *not comparable* (exit 4) unless it is named with
``--allow-difference``, and the report says which differences were allowed.

What is counted, and kept apart:

* **main** -- the unconditional ``canonical_outcome`` (pair status);
* **conditional** -- the assumption-dependent ``conditional_outcome``; a
  conditional ``NOT_EQ`` is never counted as a ``NOT_EQ``;
* **concrete difference** -- a replay that established a difference
  (``CONDITIONAL_CONCRETE_COUNTEREXAMPLE``), whatever the conditional column
  then says.  A diagnostic fact, not a verdict.

Sections: the setting each pair actually ran under against its tree's manifest;
main and conditional transitions; Eq false ``NOT_EQ`` and Neq detection (by
ground truth, and the Neq-Core view); concrete differences (pairs, function
pairs, witnesses); confirmed pairs held at conditional ``UNKNOWN`` by other
blockers, per reason, per combination and per sole remaining reason (what C6
could gain by releasing one reason); why a replay was not run or established
nothing; cost against the baseline.

Every count comes from the pair status, the result JSON in the pair log, the
runtime receipt and the run manifest.  Nothing is read as zero or as a match
when it cannot be read: missing and unreadable records are counted on their own.
The integrity section checks the aggregate against those records (the pair
status and the result JSON agree, the concrete artifact digests verify, the
reconstructed remaining blockers agree with the conditional verdict).  The
report never feeds a verdict.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    HALVES,
    LABEL_EQ,
    LABEL_NEQ,
    PairKey,
    PairOutcome,
    load_pair_outcomes,
    neq_core_excluded,
    normalized_sha256,
)

REPORT_SCHEMA = "concrete-evaluation-report-v1"
RUN_MANIFEST_FILE = "run_manifest.txt"

EXIT_OK = 0
EXIT_USAGE = 1
EXIT_NOT_COMPARABLE = 4
EXIT_INTEGRITY = 5

OUTCOME_NOT_EQ = "NOT_EQ"
OUTCOME_UNKNOWN = "UNKNOWN"

#: Decision effects that keep a conditional NOT_EQ from being issued
#: (``authority.decision.conditional.finalize_conditional_decision``).
BLOCKS_NOT_EQ = frozenset({"blocks_disequivalence", "blocks_decision"})

#: Lane states (``conditional_lane`` diagnostic) in which the concrete replay,
#: when enabled, always leaves its record.
LANE_RAN_STATES = frozenset({"issued", "non_decisive", "not_constructed", "over_receipt_bound"})

#: Environment rows of the run manifest whose difference changes what a run
#: measures (tool versions and resource limits).
ENVIRONMENT_KEYS = (
    "python_version", "ghidra_version", "java_version", "z3_version",
    "cgroup_memory_max", "cgroup_cpu_max",
)

# Witness-level classes of a replay that established nothing.
CLASS_INPUT_REFUSED = "input_refused"
CLASS_OBSERVATION_REFUSED = "observation_refused"
CLASS_HAZARD = "hazard"
CLASS_MONITOR_INCOMPLETE = "monitor_incomplete"
CLASS_LIMIT = "limit"
CLASS_DID_NOT_RETURN = "did_not_return"
CLASS_NO_DIFFERENCE = "no_difference"
CLASS_UNRECOGNISED = "unrecognised"

_LIMIT_TERMINATIONS = frozenset({"TIME_LIMIT", "STEP_LIMIT", "RESOURCE_LIMIT"})


def _concrete_vocabulary() -> Tuple[str, ...]:
    from scripts.function_tracer_pcode.proof.concrete_counterexample import (
        CONCRETE_BUDGET_EXHAUSTED,
        CONCRETE_EXECUTOR_UNAVAILABLE,
        CONCRETE_NO_DEADLINE,
        CONCRETE_NO_WITNESS,
        CONCRETE_NOT_CONFIRMED,
        CONCRETE_PLAN_REFUSED,
        CONCRETE_SIDE_UNAVAILABLE,
    )

    return (
        CONCRETE_NO_WITNESS, CONCRETE_EXECUTOR_UNAVAILABLE, CONCRETE_SIDE_UNAVAILABLE,
        CONCRETE_PLAN_REFUSED, CONCRETE_NOT_CONFIRMED, CONCRETE_BUDGET_EXHAUSTED,
        CONCRETE_NO_DEADLINE,
    )


def concrete_discharged_reason_ids() -> frozenset:
    """The reasons a concrete difference discharges (the authority's definition)."""
    from scripts.function_tracer_pcode.authority.decision.conditional_lane import (
        CONCRETE_DISCHARGED_REASON_IDS,
    )

    return frozenset(CONCRETE_DISCHARGED_REASON_IDS)


# --------------------------------------------------------------------------
# Per-pair facts (each result payload is read once)
# --------------------------------------------------------------------------


@dataclass
class PairFacts:
    """What the report needs of one pair of one tree."""

    key: PairKey
    label: str
    neq_core: bool
    outcome: str
    conditional: Optional[str]
    left_sha256: Optional[str]
    right_sha256: Optional[str]
    payload_read: bool = False
    payload_final_outcome: Optional[str] = None
    payload_conditional: Optional[str] = None
    status_receipt_conditional: Optional[str] = None
    status_receipt_occurrence: Optional[str] = None
    status_receipt_premise_kinds: Tuple[str, ...] = ()
    result_occurrence_id: Optional[str] = None
    setting: Optional[Mapping[str, Any]] = None
    lane: Optional[str] = None
    lane_skipped: Optional[str] = None
    lane_external_proof_kind: Optional[str] = None
    lane_seconds: Optional[float] = None
    concrete: Optional[Mapping[str, Any]] = None
    concrete_digest_ok: Optional[bool] = None
    blocking_reasons: Tuple[str, ...] = ()
    ground_truth: Optional[str] = None

    @property
    def function_pair(self) -> Tuple[str, str]:
        return (self.key[0], self.key[1])

    @property
    def concrete_payload(self) -> Mapping[str, Any]:
        payload = (self.concrete or {}).get("artifact_payload")
        return payload if isinstance(payload, Mapping) else {}

    @property
    def concrete_decisive(self) -> bool:
        return bool(self.concrete_payload.get("proof_kind"))

    @property
    def replays(self) -> List[Mapping[str, Any]]:
        replays = self.concrete_payload.get("replays")
        return [r for r in replays if isinstance(r, Mapping)] if isinstance(replays, list) else []

    @property
    def concrete_seconds(self) -> Optional[float]:
        diagnostics = (self.concrete or {}).get("diagnostics")
        value = diagnostics.get("seconds") if isinstance(diagnostics, Mapping) else None
        return float(value) if isinstance(value, (int, float)) and not isinstance(value, bool) else None


def _text(value: Any) -> Optional[str]:
    return value if isinstance(value, str) and value else None


def _number(value: Any) -> Optional[float]:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _receipt_facts(receipt: Any) -> Tuple[Optional[str], Optional[str], Tuple[str, ...]]:
    if not isinstance(receipt, Mapping):
        return None, None, ()
    kinds = []
    for premise in receipt.get("assumption_set") or ():
        if isinstance(premise, Mapping) and isinstance(premise.get("kind"), str):
            kinds.append(premise["kind"])
    return (
        _text(receipt.get("conditional_outcome")),
        _text(receipt.get("result_occurrence_id")),
        tuple(sorted(set(kinds))),
    )


def read_pair_facts(record: PairOutcome, ground_truth_manifest: Any = None) -> PairFacts:
    """One pair's facts from its status record and its result payload."""
    from scripts.function_tracer_pcode.proof.concrete_counterexample import (
        verify_concrete_record,
    )
    from scripts.function_tracer_pcode.reporting.outcome_transition import (
        final_result_payload,
    )

    receipt_conditional, receipt_occurrence, receipt_kinds = _receipt_facts(
        record.conditional_decision_receipt
    )
    facts = PairFacts(
        key=record.key,
        label=record.label,
        neq_core=record.label == LABEL_NEQ
        and not neq_core_excluded(record.sample_identity, record.function_name),
        outcome=record.outcome,
        conditional=record.conditional_outcome,
        left_sha256=normalized_sha256(record.left_binary_sha256),
        right_sha256=normalized_sha256(record.right_binary_sha256),
        status_receipt_conditional=receipt_conditional,
        status_receipt_occurrence=receipt_occurrence,
        status_receipt_premise_kinds=receipt_kinds,
        result_occurrence_id=record.result_occurrence_id,
    )
    if ground_truth_manifest is not None and record.label == LABEL_NEQ:
        fact, _reason = ground_truth_manifest.lookup(record.sample_identity, record.function_name)
        facts.ground_truth = getattr(fact, "semantic_ground_truth", None) if fact is not None else None
    payload = final_result_payload(record)
    if payload is None:
        return facts
    facts.payload_read = True
    facts.payload_final_outcome = _text(payload.get("final_outcome"))
    facts.payload_conditional = _text(payload.get("conditional_outcome"))
    diagnostics = payload.get("diagnostics")
    diagnostics = diagnostics if isinstance(diagnostics, Mapping) else {}
    setting = diagnostics.get("concrete_execution_setting")
    facts.setting = setting if isinstance(setting, Mapping) else None
    lane = diagnostics.get("conditional_lane")
    if isinstance(lane, Mapping):
        facts.lane = _text(lane.get("conditional_lane"))
        facts.lane_skipped = _text(lane.get("skipped"))
        facts.lane_external_proof_kind = _text(lane.get("proof_kind"))
        concrete = lane.get("concrete_replay")
        if isinstance(concrete, Mapping):
            facts.concrete = concrete
            facts.concrete_digest_ok = bool(verify_concrete_record(concrete))
    timings = diagnostics.get("timings")
    boundary = timings.get("boundary_seconds") if isinstance(timings, Mapping) else None
    if isinstance(boundary, Mapping):
        facts.lane_seconds = _number(boundary.get("conditional_lane"))
    blocking = []
    for row in payload.get("c_active_base") or ():
        if (
            isinstance(row, Mapping)
            and row.get("decision_effect") in BLOCKS_NOT_EQ
            and isinstance(row.get("reason_id"), str)
        ):
            blocking.append(row["reason_id"])
    facts.blocking_reasons = tuple(blocking)
    return facts


# --------------------------------------------------------------------------
# Trees and their conditions
# --------------------------------------------------------------------------


@dataclass
class Tree:
    root: Path
    #: ``None`` for a matrix tree, else the half (``eq`` / ``neq``) of a subset run.
    scopes: Dict[Optional[str], Path]
    manifests: Dict[Optional[str], Dict[str, str]]
    records: Dict[PairKey, PairOutcome]
    facts: Dict[PairKey, PairFacts] = field(default_factory=dict)

    def manifest_for(self, record: PairOutcome) -> Mapping[str, str]:
        return self.manifests.get(record.half, self.manifests.get(None, {}))


def _tree_scopes(root: Path) -> Dict[Optional[str], Path]:
    if (root / RUN_MANIFEST_FILE).is_file():
        return {None: root}
    scopes = {half: root / half for half in HALVES if (root / half / RUN_MANIFEST_FILE).is_file()}
    return scopes or {None: root}


def load_tree(root: Path) -> Tree:
    from scripts.function_tracer_pcode.reporting.outcome_transition import load_ground_truth
    from scripts.function_tracer_pcode.reporting.verification_ledger import (
        read_key_value_manifest,
    )

    root = Path(root)
    scopes = _tree_scopes(root)
    manifests = {
        scope: dict(read_key_value_manifest(path / RUN_MANIFEST_FILE)) for scope, path in scopes.items()
    }
    tree = Tree(root=root, scopes=scopes, manifests=manifests, records=load_pair_outcomes(root))
    truths = {scope: load_ground_truth(path)[0] for scope, path in scopes.items()}
    for key, record in tree.records.items():
        truth = truths.get(record.half, truths.get(None))
        tree.facts[key] = read_pair_facts(record, truth)
    return tree


@dataclass(frozen=True)
class ConditionCheck:
    name: str
    status: str  # same / differs / unavailable
    baseline: Any = None
    treatment: Any = None
    allowed: bool = False

    @property
    def blocking(self) -> bool:
        return self.status != "same" and not self.allowed

    def as_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name, "status": self.status, "allowed": self.allowed,
            "baseline": self.baseline, "treatment": self.treatment,
        }


def _analysis_config(manifest: Mapping[str, str]) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        analysis_config_from_run,
    )

    try:
        return dict(analysis_config_from_run(manifest)), None
    except (KeyError, ValueError) as exc:
        return None, str(exc)


def concrete_setting_of(manifest: Mapping[str, str]) -> Dict[str, Optional[str]]:
    """The tree's effective concrete setting, as its run manifest records it."""
    from scripts.function_tracer_pcode.reporting.runner_concrete_policy import (
        KEY_BUDGET,
        KEY_INACTIVE_REASON,
        KEY_STAGES,
        KEY_STAGES_REQUESTED,
    )

    return {
        "stages": manifest.get(KEY_STAGES),
        "budget": manifest.get(KEY_BUDGET),
        "requested_stages": manifest.get(KEY_STAGES_REQUESTED),
        "inactive_reason": manifest.get(KEY_INACTIVE_REASON),
    }


def compare_conditions(
    baseline: Tree, treatment: Tree, allowed: Iterable[str] = (),
) -> List[ConditionCheck]:
    """Every condition two trees must share to compare their concrete setting only."""
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        ANALYSIS_CONFIG_CONCRETE_FIELDS,
    )
    from scripts.function_tracer_pcode.reporting.outcome_transition import tree_completeness

    allowed = set(allowed)
    checks: List[ConditionCheck] = []

    def add(name: str, base: Any, treat: Any, *, unavailable: bool = False) -> None:
        status = "unavailable" if unavailable else ("same" if base == treat else "differs")
        checks.append(ConditionCheck(name, status, base, treat, name in allowed))

    scopes = sorted(set(baseline.scopes) | set(treatment.scopes), key=lambda s: s or "")
    add("scopes", sorted(s or "" for s in baseline.scopes), sorted(s or "" for s in treatment.scopes))
    for scope in scopes:
        prefix = f"{scope}." if scope else ""
        base_m = baseline.manifests.get(scope, {})
        treat_m = treatment.manifests.get(scope, {})
        for side_name, manifest in (("baseline", base_m), ("treatment", treat_m)):
            start = manifest.get("analysis_source_digest_start")
            end = manifest.get("analysis_source_digest_end")
            if start is None or start != end:
                add(f"{prefix}source_stable.{side_name}", start, end, unavailable=start is None or end is None)
        add(f"{prefix}source_digest", base_m.get("analysis_source_digest_start"),
            treat_m.get("analysis_source_digest_start"),
            unavailable=not (base_m.get("analysis_source_digest_start")
                             and treat_m.get("analysis_source_digest_start")))
        base_c, base_err = _analysis_config(base_m)
        treat_c, treat_err = _analysis_config(treat_m)
        if base_c is None or treat_c is None:
            add(f"{prefix}analysis_config", base_err, treat_err, unavailable=True)
        else:
            fields = sorted((set(base_c) | set(treat_c)) - set(ANALYSIS_CONFIG_CONCRETE_FIELDS) - {"schema"})
            for name in fields:
                if base_c.get(name) != treat_c.get(name):
                    add(f"{prefix}analysis_config.{name}", base_c.get(name), treat_c.get(name))
            add(f"{prefix}analysis_config.schema", base_c.get("schema"), treat_c.get("schema"))
            recorded = all("concrete_stages" in c for c in (base_c, treat_c))
            if not recorded:
                add(f"{prefix}concrete_setting_recorded",
                    "concrete_stages" in base_c, "concrete_stages" in treat_c, unavailable=True)
        for key in ENVIRONMENT_KEYS:
            if base_m.get(key) != treat_m.get(key):
                add(f"{prefix}environment.{key}", base_m.get(key), treat_m.get(key))
        for side_name, tree in (("baseline", baseline), ("treatment", treatment)):
            path = tree.scopes.get(scope)
            if path is None:
                continue
            completeness = tree_completeness(path)
            if completeness.status != "complete":
                add(f"{prefix}completeness.{side_name}", completeness.status, completeness.detail,
                    unavailable=True)
    base_keys, treat_keys = set(baseline.records), set(treatment.records)
    add("pair_set", len(base_keys - treat_keys), len(treat_keys - base_keys))
    differing = unverifiable = 0
    for key in sorted(base_keys & treat_keys):
        b, t = baseline.facts[key], treatment.facts[key]
        sides = (b.left_sha256, b.right_sha256, t.left_sha256, t.right_sha256)
        if any(value is None for value in sides):
            unverifiable += 1
        elif (b.left_sha256, b.right_sha256) != (t.left_sha256, t.right_sha256):
            differing += 1
    add("binaries.differing_pairs", 0, differing)
    if unverifiable:
        add("binaries.unverifiable_pairs", 0, unverifiable, unavailable=True)
    return checks


# --------------------------------------------------------------------------
# The setting each pair ran under, against its tree's manifest
# --------------------------------------------------------------------------


def setting_check(tree: Tree) -> Dict[str, Any]:
    """Does every pair's own record show the setting its tree's manifest declares?"""
    counts: Counter = Counter()
    examples: List[str] = []
    stage_record_anomalies = 0
    for key, record in tree.records.items():
        facts = tree.facts[key]
        manifest = concrete_setting_of(tree.manifest_for(record))
        declared = manifest["stages"]
        if not facts.payload_read:
            counts["no_result_payload"] += 1
            continue
        if facts.setting is None:
            counts["record_missing"] += 1
            continue
        effective = facts.setting.get("effective_stages")
        effective_text = ",".join(effective) if isinstance(effective, list) and effective else "none"
        budget_ok = True
        if effective_text != "none":
            try:
                budget_ok = math.isclose(float(manifest["budget"] or "nan"),
                                         float(facts.setting.get("budget_seconds")))
            except (TypeError, ValueError):
                budget_ok = False
        if declared is None:
            counts["manifest_unrecorded"] += 1
        elif effective_text == declared and budget_ok:
            counts["agrees"] += 1
        else:
            counts["disagrees"] += 1
            if len(examples) < 10:
                examples.append(f"{'/'.join(key)}: manifest {declared} record {effective_text}")
        stage_on = effective_text != "none"
        if facts.concrete is not None and not stage_on:
            stage_record_anomalies += 1
        if stage_on and facts.lane in LANE_RAN_STATES and facts.concrete is None:
            stage_record_anomalies += 1
    return {
        "pairs": len(tree.records),
        "counts": dict(sorted(counts.items())),
        "replay_records_inconsistent_with_setting": stage_record_anomalies,
        "examples": examples,
        "ok": counts["disagrees"] == 0 and counts["record_missing"] == 0
        and counts["manifest_unrecorded"] == 0 and stage_record_anomalies == 0,
    }


# --------------------------------------------------------------------------
# Classification of the concrete replay of one pair
# --------------------------------------------------------------------------


def witness_class(replay: Mapping[str, Any]) -> Tuple[str, str]:
    """``(class, detail)`` of a replay that established nothing."""
    status = replay.get("status")
    reason = str(replay.get("reason") or "")
    if status == "INPUT_REFUSED":
        return CLASS_INPUT_REFUSED, reason
    parts = reason.split(":")
    head = parts[0]
    if head == "NO_DIFFERENCE_OBSERVED":
        return CLASS_NO_DIFFERENCE, reason
    if head in ("RUN_HAS_HAZARD", "WRITABLE_IMAGE_READ"):
        return CLASS_HAZARD, reason
    if head.endswith("_NOT_TRACKED"):
        return CLASS_MONITOR_INCOMPLETE, reason
    if head in ("OBSERVATION_REFUSED", "OBSERVATION_MISSING"):
        return CLASS_OBSERVATION_REFUSED, reason
    if head == "RUN_DID_NOT_RETURN":
        if any(part in _LIMIT_TERMINATIONS for part in parts[1:]):
            return CLASS_LIMIT, reason
        return CLASS_DID_NOT_RETURN, reason
    return CLASS_UNRECOGNISED, reason


def pair_funnel_class(facts: PairFacts) -> Tuple[str, str]:
    """``(class, detail)``: where this pair left the concrete replay (mutually exclusive)."""
    (no_witness, executor_unavailable, side_unavailable, plan_refused,
     not_confirmed, budget_exhausted, no_deadline) = _concrete_vocabulary()
    if facts.outcome != OUTCOME_UNKNOWN:
        return "not_eligible", f"main {facts.outcome}"
    if not facts.payload_read:
        return "no_result_payload", ""
    if facts.lane_skipped:
        return "lane_not_run", facts.lane_skipped
    if facts.lane is None:
        return "lane_not_run", "no_lane_record"
    if facts.concrete is None:
        if facts.lane in LANE_RAN_STATES:
            return "stage_off", facts.lane
        return "lane_stopped", facts.lane
    payload = facts.concrete_payload
    if payload.get("proof_kind"):
        return "confirmed", ""
    reasons = [str(r) for r in payload.get("non_decisive_reasons") or ()]
    first = reasons[0] if reasons else ""
    plan = str(payload.get("plan") or "")
    if first == no_witness:
        return "no_witness", ""
    if first == no_deadline:
        return "not_run_no_deadline", ""
    if first == budget_exhausted:
        return "not_run_budget_exhausted", ""
    if first == executor_unavailable:
        return "executor_unavailable", ""
    if first == side_unavailable:
        return "side_unavailable", plan.split(":", 2)[-1].split(":")[0] if plan else ""
    if first == plan_refused:
        stage = plan.split(":", 1)[0]
        if stage in ("INPUT_SURFACE", "INPUT_CORRESPONDENCE"):
            return "plan_refused_input", plan
        return "plan_refused_observation", plan
    if first == not_confirmed:
        classes = sorted({witness_class(r)[0] for r in facts.replays})
        detail = "+".join(classes) if classes else "no_replay"
        if budget_exhausted in reasons:
            detail += "+budget_exhausted"
        return "replayed_no_evidence", detail
    return "unrecognised", ",".join(reasons)


def remaining_blockers(facts: PairFacts, discharged: frozenset) -> Optional[Tuple[str, ...]]:
    """The reasons still blocking a conditional NOT_EQ after the concrete discharge.

    ``None`` when they cannot be reconstructed from the result JSON alone: the
    external-call lane was decisive too, and its discharges are not recorded per row.
    """
    if facts.lane_external_proof_kind:
        return None
    return tuple(sorted({r for r in facts.blocking_reasons if r not in discharged}))


# --------------------------------------------------------------------------
# Sections
# --------------------------------------------------------------------------


def _distribution(values: Sequence[float]) -> Dict[str, Any]:
    if not values:
        return {"n": 0}
    ordered = sorted(values)

    def q(p: float) -> float:
        return round(ordered[min(len(ordered) - 1, int(p * len(ordered)))], 4)

    return {
        "n": len(ordered), "sum": round(sum(ordered), 4), "mean": round(sum(ordered) / len(ordered), 4),
        "p50": q(0.5), "p90": q(0.9), "p99": q(0.99), "max": round(ordered[-1], 4),
    }


def _pairs_and_functions(facts: Iterable[PairFacts]) -> Dict[str, int]:
    facts = list(facts)
    return {"pairs": len(facts), "function_pairs": len({f.function_pair for f in facts})}


def detection(tree: Tree) -> Dict[str, Any]:
    """Main / conditional / concrete-difference counts per label, ground truth and Neq-Core."""

    def tiers(selection: List[PairFacts]) -> Dict[str, Any]:
        return {
            "pairs": len(selection),
            "function_pairs": len({f.function_pair for f in selection}),
            "main_not_eq": _pairs_and_functions(f for f in selection if f.outcome == OUTCOME_NOT_EQ),
            "conditional_not_eq": _pairs_and_functions(
                f for f in selection if f.conditional == OUTCOME_NOT_EQ),
            "conditional_not_eq_without_main": _pairs_and_functions(
                f for f in selection if f.conditional == OUTCOME_NOT_EQ and f.outcome != OUTCOME_NOT_EQ),
            "concrete_difference": _pairs_and_functions(f for f in selection if f.concrete_decisive),
            "main_or_conditional_not_eq": _pairs_and_functions(
                f for f in selection if OUTCOME_NOT_EQ in (f.outcome, f.conditional)),
            "main_outcomes": dict(sorted(Counter(f.outcome for f in selection).items())),
            "conditional_outcomes": dict(sorted(Counter(
                f.conditional or "NONE" for f in selection).items())),
        }

    all_facts = list(tree.facts.values())
    eq = [f for f in all_facts if f.label == LABEL_EQ]
    neq = [f for f in all_facts if f.label == LABEL_NEQ]
    view: Dict[str, Any] = {"eq": tiers(eq), "neq": tiers(neq),
                            "neq_core": tiers([f for f in neq if f.neq_core])}
    by_truth: Dict[str, List[PairFacts]] = {}
    for f in neq:
        by_truth.setdefault(f.ground_truth or "unreviewed", []).append(f)
    view["neq_by_ground_truth"] = {truth: tiers(sel) for truth, sel in sorted(by_truth.items())}
    false_not_eq = [
        "/".join(f.key) + f" main={f.outcome} conditional={f.conditional} concrete={f.concrete_decisive}"
        for f in eq if OUTCOME_NOT_EQ in (f.outcome, f.conditional) or f.concrete_decisive
    ]
    contradicted = [
        "/".join(f.key) for f in neq
        if f.ground_truth == "CONFIRMED_EQ" and (OUTCOME_NOT_EQ in (f.outcome, f.conditional) or f.concrete_decisive)
    ]
    view["eq_false_not_eq"] = {
        "main": sum(f.outcome == OUTCOME_NOT_EQ for f in eq),
        "conditional": sum(f.conditional == OUTCOME_NOT_EQ for f in eq),
        "concrete_difference": sum(f.concrete_decisive for f in eq),
        "pairs": false_not_eq[:50],
    }
    view["neq_confirmed_eq_contradicted"] = contradicted[:50]
    return view


def against_baseline(baseline: Tree, treatment: Tree) -> Dict[str, Any]:
    """Detection of the treatment against the SMT-only baseline, as pair / function-pair sets.

    ``gained_*``: decided ``NOT_EQ`` in the treatment (main, or conditional only) but not a
    main ``NOT_EQ`` in the baseline.  ``lost_main``: a baseline main ``NOT_EQ`` the
    treatment does not have (run-to-run variation; the replay runs after the decision).
    ``difference_only``: a concrete difference neither column turned into ``NOT_EQ``.
    """

    common = sorted(set(baseline.facts) & set(treatment.facts))

    def view(select) -> Dict[str, Any]:
        keys = [k for k in common if select(baseline.facts[k], treatment.facts[k])]
        functions = {treatment.facts[k].function_pair for k in keys}
        return {"pairs": len(keys), "function_pairs": len(functions)}

    def groups(label_filter) -> Dict[str, Any]:
        def sel(rule):
            return view(lambda b, t: label_filter(t) and rule(b, t))
        return {
            "baseline_main_not_eq": sel(lambda b, t: b.outcome == OUTCOME_NOT_EQ),
            "treatment_main_not_eq": sel(lambda b, t: t.outcome == OUTCOME_NOT_EQ),
            "gained_main": sel(lambda b, t: t.outcome == OUTCOME_NOT_EQ and b.outcome != OUTCOME_NOT_EQ),
            "gained_conditional_only": sel(
                lambda b, t: t.conditional == OUTCOME_NOT_EQ and OUTCOME_NOT_EQ not in (t.outcome, b.outcome)),
            "lost_main": sel(lambda b, t: b.outcome == OUTCOME_NOT_EQ and t.outcome != OUTCOME_NOT_EQ),
            "difference_only": sel(
                lambda b, t: t.concrete_decisive and OUTCOME_NOT_EQ not in (t.outcome, t.conditional)),
        }

    return {
        "pairs_compared": len(common),
        "eq": groups(lambda f: f.label == LABEL_EQ),
        "neq": groups(lambda f: f.label == LABEL_NEQ),
        "neq_core": groups(lambda f: f.neq_core),
        "note": "a conditional NOT_EQ is reported apart from main NOT_EQ and never added to it",
    }


def concrete_differences(tree: Tree) -> Dict[str, Any]:
    confirmed = [f for f in tree.facts.values() if f.concrete_decisive]
    witnesses = 0
    digests: Set[str] = set()
    for f in confirmed:
        for replay in f.replays:
            if replay.get("status") == "CONFIRMED":
                witnesses += 1
                digest = replay.get("witness_digest")
                if isinstance(digest, str):
                    digests.add(digest)
    by_label = {
        label: _pairs_and_functions(f for f in confirmed if f.label == label)
        for label in (LABEL_EQ, LABEL_NEQ)
    }
    return {
        **_pairs_and_functions(confirmed),
        "by_label": by_label,
        "confirmed_witness_replays": witnesses,
        "distinct_confirmed_witnesses": len(digests),
        "conditional_of_confirmed": dict(sorted(Counter(
            f.conditional or "NONE" for f in confirmed).items())),
    }


def blocked(tree: Tree) -> Dict[str, Any]:
    """Confirmed pairs whose conditional column stayed short of NOT_EQ, and why."""
    discharged = concrete_discharged_reason_ids()
    per_reason: Counter = Counter()
    per_reason_functions: Dict[str, Set[Tuple[str, str]]] = {}
    sole: Counter = Counter()
    combos: Counter = Counter()
    consistency: Counter = Counter()
    not_reconstructible = 0
    held = []
    for f in tree.facts.values():
        if not f.concrete_decisive:
            continue
        rest = remaining_blockers(f, discharged)
        if rest is None:
            not_reconstructible += 1
            continue
        issued_not_eq = f.conditional == OUTCOME_NOT_EQ
        if issued_not_eq == (not rest):
            consistency["agrees"] += 1
        else:
            consistency["disagrees"] += 1
        if issued_not_eq:
            continue
        held.append(f)
        combos[",".join(rest) or "<none>"] += 1
        for reason in rest:
            per_reason[reason] += 1
            per_reason_functions.setdefault(reason, set()).add(f.function_pair)
        if len(rest) == 1:
            sole[rest[0]] += 1
    return {
        **_pairs_and_functions(held),
        "by_label": {label: _pairs_and_functions(f for f in held if f.label == label)
                     for label in (LABEL_EQ, LABEL_NEQ)},
        "per_reason": {reason: {"pairs": count,
                                "function_pairs": len(per_reason_functions[reason]),
                                "sole_remaining_reason_pairs": sole.get(reason, 0)}
                       for reason, count in per_reason.most_common()},
        "combinations": dict(combos.most_common()),
        "reconstruction": {**dict(consistency), "not_reconstructible": not_reconstructible},
        "discharged_by_concrete": sorted(discharged),
        "note": ("sole_remaining_reason_pairs: confirmed pairs that would reach conditional NOT_EQ "
                 "if that one reason were also discharged (C6 material, not a decision)"),
    }


def funnel(tree: Tree) -> Dict[str, Any]:
    classes: Counter = Counter()
    details: Dict[str, Counter] = {}
    witness_classes: Counter = Counter()
    witness_details: Counter = Counter()
    terminations: Counter = Counter()
    for f in tree.facts.values():
        cls, detail = pair_funnel_class(f)
        classes[cls] += 1
        if detail:
            details.setdefault(cls, Counter())[detail] += 1
        if f.concrete is None:
            continue
        for replay in f.replays:
            for result in replay.get("results") or ():
                if isinstance(result, Mapping) and isinstance(result.get("termination"), str):
                    terminations[result["termination"]] += 1
            if replay.get("status") == "CONFIRMED":
                witness_classes["confirmed"] += 1
                continue
            wcls, wdetail = witness_class(replay)
            witness_classes[wcls] += 1
            witness_details[f"{wcls} {wdetail}"] += 1
    return {
        "pairs": dict(classes.most_common()),
        "pair_details": {cls: dict(counter.most_common(30)) for cls, counter in sorted(details.items())},
        "witnesses": dict(witness_classes.most_common()),
        "witness_details": dict(witness_details.most_common(40)),
        "run_terminations": dict(terminations.most_common()),
    }


def cost(baseline: Tree, treatment: Tree) -> Dict[str, Any]:
    from scripts.function_tracer_pcode.reporting.outcome_transition import load_runtime_metrics

    base, base_unusable = load_runtime_metrics(baseline.root)
    treat, treat_unusable = load_runtime_metrics(treatment.root)
    common = sorted(set(base) & set(treat) & set(baseline.records) & set(treatment.records))
    deltas = [treat[k] - base[k] for k in common]
    replayed = [k for k in common if treatment.facts[k].concrete is not None
                and treatment.facts[k].replays]
    return {
        "wall_seconds": {
            "baseline": _distribution([base[k] for k in common]),
            "treatment": _distribution([treat[k] for k in common]),
            "delta_treatment_minus_baseline": _distribution(deltas),
            "delta_on_pairs_with_replays": _distribution([treat[k] - base[k] for k in replayed]),
            "pairs_measured_on_both_sides": len(common),
            "unusable_receipts": {"baseline": base_unusable, "treatment": treat_unusable},
        },
        "concrete_replay_seconds": _distribution([
            s for f in treatment.facts.values() if (s := f.concrete_seconds) is not None]),
        "conditional_lane_seconds": {
            "baseline": _distribution([s for f in baseline.facts.values()
                                       if (s := f.lane_seconds) is not None]),
            "treatment": _distribution([s for f in treatment.facts.values()
                                        if (s := f.lane_seconds) is not None]),
        },
        "timeouts": {
            "baseline": sum(f.outcome == "TIMEOUT" for f in baseline.facts.values()),
            "treatment": sum(f.outcome == "TIMEOUT" for f in treatment.facts.values()),
        },
        "informational_only": True,
    }


def integrity(tree: Tree) -> Dict[str, Any]:
    """The aggregate's inputs agree with each other, pair by pair."""
    counts: Counter = Counter()
    examples: List[str] = []

    def bad(name: str, key: PairKey) -> None:
        counts[name] += 1
        if len(examples) < 20:
            examples.append(f"{name}: {'/'.join(key)}")

    for key, f in tree.facts.items():
        if not f.payload_read:
            continue
        if (f.conditional or None) != (f.payload_conditional or None):
            bad("status_conditional_vs_result_json", key)
        if f.conditional is not None and f.status_receipt_conditional != f.conditional:
            bad("status_conditional_vs_its_receipt", key)
        if (f.status_receipt_occurrence and f.result_occurrence_id
                and f.status_receipt_occurrence != f.result_occurrence_id):
            bad("conditional_receipt_occurrence", key)
        if f.concrete is not None and not f.concrete_digest_ok:
            bad("concrete_artifact_digest", key)
        if f.concrete_decisive and f.conditional is not None and not any(
            kind.startswith("CONCRETE_") for kind in f.status_receipt_premise_kinds
        ):
            bad("confirmed_without_concrete_premises", key)
        if (f.payload_final_outcome is not None and f.outcome in ("EQUIVALENT", "NOT_EQ", "UNKNOWN")
                and f.payload_final_outcome != f.outcome):
            bad("status_main_vs_result_json", key)
    return {"pairs_with_payload": sum(f.payload_read for f in tree.facts.values()),
            "failures": dict(sorted(counts.items())), "examples": examples,
            "ok": not counts}


def transitions(baseline: Tree, treatment: Tree) -> Dict[str, Any]:
    from scripts.function_tracer_pcode.reporting.outcome_transition import build_transition

    report = build_transition(baseline.records, treatment.records)
    main_changes = [
        f"{row.sample_identity}/{row.function_name}/{row.pair_id}: {row.before} -> {row.after}"
        for row in report.changed_rows
    ]
    return {
        "main": report.as_dict(),
        "main_changed_pairs": main_changes[:100],
        "note": ("concrete execution runs after the unconditional decision, so a main change "
                 "between the two trees is run-to-run variation (#161, #183, load), not its effect"),
    }


# --------------------------------------------------------------------------
# Report
# --------------------------------------------------------------------------


def build_report(baseline_root: Path, treatment_root: Path, allowed: Sequence[str] = ()) -> Dict[str, Any]:
    return build_report_from_trees(load_tree(baseline_root), load_tree(treatment_root), allowed)


def build_report_from_trees(baseline: Tree, treatment: Tree, allowed: Sequence[str] = ()) -> Dict[str, Any]:
    checks = compare_conditions(baseline, treatment, allowed)
    settings = {
        "baseline": {scope or "": concrete_setting_of(m) for scope, m in baseline.manifests.items()},
        "treatment": {scope or "": concrete_setting_of(m) for scope, m in treatment.manifests.items()},
    }
    report = {
        "schema": REPORT_SCHEMA,
        "baseline": str(baseline.root),
        "treatment": str(treatment.root),
        "concrete_settings": settings,
        "conditions": {
            "comparable": not any(check.blocking for check in checks),
            "checks": [check.as_dict() for check in checks],
            "allowed": sorted(set(allowed)),
        },
        "setting_records": {"baseline": setting_check(baseline), "treatment": setting_check(treatment)},
        "integrity": {"baseline": integrity(baseline), "treatment": integrity(treatment)},
        "transitions": transitions(baseline, treatment),
        "detection": {"baseline": detection(baseline), "treatment": detection(treatment)},
        "against_baseline": against_baseline(baseline, treatment),
        "concrete_differences": concrete_differences(treatment),
        "blocked": blocked(treatment),
        "funnel": funnel(treatment),
        "cost": cost(baseline, treatment),
    }
    return report


def report_exit_code(report: Mapping[str, Any]) -> int:
    if not report["conditions"]["comparable"]:
        return EXIT_NOT_COMPARABLE
    sides = ("baseline", "treatment")
    if not all(report["setting_records"][s]["ok"] and report["integrity"][s]["ok"] for s in sides):
        return EXIT_INTEGRITY
    if report["blocked"]["reconstruction"].get("disagrees"):
        return EXIT_INTEGRITY
    return EXIT_OK


def pair_rows(baseline: Tree, treatment: Tree) -> List[str]:
    """One TSV row per pair (for audits outside the report)."""
    discharged = concrete_discharged_reason_ids()
    rows = ["\t".join((
        "sample", "function", "left", "right", "label", "ground_truth",
        "baseline_main", "treatment_main", "baseline_conditional", "treatment_conditional",
        "funnel", "funnel_detail", "concrete_difference", "remaining_blockers",
    ))]
    for key in sorted(set(baseline.facts) | set(treatment.facts)):
        b = baseline.facts.get(key)
        t = treatment.facts.get(key)
        ref = t or b
        cls, detail = pair_funnel_class(t) if t else ("missing", "")
        rest = remaining_blockers(t, discharged) if t and t.concrete_decisive else ()
        rows.append("\t".join((
            *key, ref.label, ref.ground_truth or "",
            b.outcome if b else "MISSING", t.outcome if t else "MISSING",
            (b.conditional or "NONE") if b else "MISSING", (t.conditional or "NONE") if t else "MISSING",
            cls, detail, "1" if t and t.concrete_decisive else "0",
            "?" if rest is None else ",".join(rest),
        )))
    return rows


def format_report(report: Mapping[str, Any]) -> str:
    lines = [f"concrete evaluation ({report['schema']})",
             f"  baseline : {report['baseline']}", f"  treatment: {report['treatment']}"]
    for side, scopes in report["concrete_settings"].items():
        for scope, value in scopes.items():
            lines.append(f"  {side}{'/' + scope if scope else ''} concrete: {value}")
    cond = report["conditions"]
    lines.append(f"conditions: {'COMPARABLE' if cond['comparable'] else 'NOT COMPARABLE'}")
    for check in cond["checks"]:
        if check["status"] != "same":
            mark = "allowed" if check["allowed"] else "BLOCKING"
            lines.append(f"  [{mark}] {check['name']} {check['status']}: "
                         f"{check['baseline']!r} -> {check['treatment']!r}")
    for section in ("setting_records", "integrity"):
        for side, value in report[section].items():
            lines.append(f"{section} {side}: ok={value['ok']} "
                         f"{value.get('counts') or value.get('failures')}")
    trans = report["transitions"]
    matrix = {f"{row['before']}->{row['after']}": row["count"] for row in trans["main"].get("matrix", [])}
    lines.append(f"main transitions: {matrix}")
    lines.append(f"  changed: {len(trans['main_changed_pairs'])} listed ({trans['note']})")
    for side in ("baseline", "treatment"):
        det = report["detection"][side]
        lines.append(f"detection {side}: Eq false NOT_EQ {det['eq_false_not_eq']['main']} main / "
                     f"{det['eq_false_not_eq']['conditional']} conditional / "
                     f"{det['eq_false_not_eq']['concrete_difference']} concrete")
        for view in ("neq", "neq_core"):
            v = det[view]
            lines.append(f"  {view}: pairs {v['pairs']} main NOT_EQ {v['main_not_eq']} conditional "
                         f"NOT_EQ {v['conditional_not_eq']} concrete {v['concrete_difference']}")
    for view in ("eq", "neq", "neq_core"):
        lines.append(f"against baseline {view}: {report['against_baseline'][view]}")
    cd = report["concrete_differences"]
    lines.append(f"concrete differences: {cd['pairs']} pairs / {cd['function_pairs']} function pairs / "
                 f"{cd['confirmed_witness_replays']} witnesses; conditional {cd['conditional_of_confirmed']}")
    bl = report["blocked"]
    lines.append(f"confirmed but held: {bl['pairs']} pairs / {bl['function_pairs']} function pairs; "
                 f"reconstruction {bl['reconstruction']}")
    for reason, value in bl["per_reason"].items():
        lines.append(f"  {reason}: {value}")
    lines.append(f"funnel: {report['funnel']['pairs']}")
    lines.append(f"witnesses: {report['funnel']['witnesses']}")
    c = report["cost"]
    lines.append(f"wall delta: {c['wall_seconds']['delta_treatment_minus_baseline']}")
    lines.append(f"replay seconds: {c['concrete_replay_seconds']}; timeouts {c['timeouts']}")
    return "\n".join(lines) + "\n"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--baseline", required=True, type=Path,
                        help="result tree without the concrete stages under evaluation")
    parser.add_argument("--treatment", required=True, type=Path,
                        help="result tree with them, otherwise run under the same conditions")
    parser.add_argument("--json", type=Path, default=None, help="write the report as JSON")
    parser.add_argument("--pairs", type=Path, default=None, help="write one TSV row per pair")
    parser.add_argument("--allow-difference", action="append", default=[], metavar="NAME",
                        help="a condition check (by the name the report prints) whose difference "
                             "is accepted; repeat for each")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    for path in (args.baseline, args.treatment):
        if not path.is_dir():
            print(f"error: not a directory: {path}", file=sys.stderr)
            return EXIT_USAGE
    try:
        baseline, treatment = load_tree(args.baseline), load_tree(args.treatment)
        report = build_report_from_trees(baseline, treatment, args.allow_difference)
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_USAGE
    if args.json is not None:
        args.json.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    if args.pairs is not None:
        args.pairs.write_text("\n".join(pair_rows(baseline, treatment)) + "\n", encoding="utf-8")
    sys.stdout.write(format_report(report))
    return report_exit_code(report)


if __name__ == "__main__":
    sys.exit(main())
