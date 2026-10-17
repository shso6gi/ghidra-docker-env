# -*- coding: utf-8 -*-
"""左右の binary の値の比較の棚卸しと、pair を閉じる経路の静的 guard（plan v4 PR-P、U4・U14）。

* **棚卸し**（U4）: ``_cross_binary_scan`` が見つける左右の比較の node を、baseline
  （``tests/fixtures/cross_binary/comparisons.json``）と完全に一致させる。新しい node も、消えた
  entry も不合格（baseline は走査で作り直し、手で足さない）。entry ごとに role を持つ。role は
  呼び手を読んで決めた分類（理由は entry の ``why``）で、到達可能性そのものはこの test では
  確かめない。この test が機械的に確かめるのは、role が名指す関所（``CHOKEPOINTS``）が存在して
  gate を呼ぶこと、closure の validator が全て関所を通ること。``UNGATED`` の role は置かない
  （見つけたら gate の下へ移す）。新しい比較の node は分類なしには入らない。
* **closure の経路**（U14）: pair を「閉じた」と数えるのは ledger の closure だけで、closure を
  作るのは ``record_pair_closed`` だけ（最終の EQ gate はそこで封印した左右の同一視を読む）。

census の 0 件やこの test の通過は安全性の証明ではない（安全性は ``test_cross_side_identity_gate``
の反例・対照・production 経路が示す）。この test は、棚卸しの外に新しい比較が増えないこと、
gate を迂回して pair を閉じる経路が増えないことを固定する。
"""

from __future__ import annotations

import ast
import collections
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.tests.unit._cross_binary_scan import PACKAGE_ROOT, scan_keys

BASELINE_PATH = PACKAGE_ROOT / "tests" / "fixtures" / "cross_binary" / "comparisons.json"

#: owner を含まない同一視を判定へ通す関所。key は baseline の ``gated:<key>``、値は
#: (関所の関数がある file, 関数名, その関数が呼ぶ gate の名前)。
CHOKEPOINTS = {
    # 発行する site: owner を含まない closure・証拠・query の等式は、ここで出す証明書なしに作れない
    # （ledger・証拠の束縛・等式の登録が証明書を要求する）。
    "G1": ("proof/obligations/pair_closure_producers.py", "_owner_free_identity_certificate", "certify_owner_free_identity"),
    # 採用: 証拠の証明書が発行済みで、対象・比較・relation を覆うときだけ採用する。
    "G2": ("proof/formula/input_correspondence/binding.py", "_identification_is_justified", "positional_identity_gate"),
    "G3": ("proof/strategies/pairwise_services/auxiliary_smt.py", "_impl__collect_intrinsic_parameter_specs", "owner_free_identity_gate"),
    "G4": ("proof/strategies/pairwise_services/readonly_reduction.py", "_impl__readonly_contract_pairwise_extra_assertions", "certify_owner_free_identity"),
    "G5": ("proof/strategies/pairwise_services/unresolved_lowering.py", "_impl__try_build_unresolved_deferred_call_lowering", "certify_owner_free_identity"),
    "G6": ("proof/strategies/pairwise_solver_proven_rewrite.py", "try_solver_proven_rewrite_equivalence", "certify_owner_free_identity"),
    "G7": ("proof/strategies/loop_template.py", "_try_normalization_equivalence", "certify_owner_free_identity"),
    "G8": ("proof/strategies/pairwise_services/orchestration.py", "produce", "owner_free_identity_gate"),
    "G9": ("authority/domains/abi_width_readonly.py", "_positional_parameter_identity_holds", "positional_parameter_identity_gate"),
    "G10": ("proof/strategies/proof_gates/call_effect.py", "_impl__record_completed_call_effect_summary_proof_if_safe", "certify_owner_free_identity"),
    "G11": ("proof/call_effect/producer.py", "_require_positional_parameter_locations", "positional_pairing_gate"),
}

ROLES = frozenset({
    *(f"gated:{key}" for key in CHOKEPOINTS),
    "single_side", "scalar_or_tag", "correspondence", "owner_bearing", "candidate_filter", "diagnostic",
})


def _baseline():
    return json.loads(BASELINE_PATH.read_text(encoding="utf-8"))


def _key(entry):
    return (entry["path"], entry["qualname"], entry["kind"], entry["digest"])


def test_the_comparison_inventory_matches_the_baseline_exactly():
    scanned = collections.Counter(scan_keys())
    pinned = collections.Counter(_key(entry) for entry in _baseline())
    new = sorted((scanned - pinned).elements())
    stale = sorted((pinned - scanned).elements())
    assert not new, (
        "new left/right comparison(s): put an owner-free identification under the gate "
        "(proof/formula/input_correspondence/gate.py) and classify it in the baseline: " + repr(new)
    )
    assert not stale, "baseline entries that no longer exist: remove them from the baseline: " + repr(stale)


def test_every_baseline_entry_has_a_known_role_and_a_reason():
    for entry in _baseline():
        assert entry["role"] in ROLES, entry
        assert entry.get("why"), entry


def _function_calls(path: str, function: str):
    tree = ast.parse((PACKAGE_ROOT / path).read_text(encoding="utf-8"))
    found = [node for node in ast.walk(tree) if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == function]
    assert found, f"chokepoint {path}:{function} does not exist"
    return {
        (call.func.attr if isinstance(call.func, ast.Attribute) else getattr(call.func, "id", ""))
        for node in found for call in ast.walk(node) if isinstance(call, ast.Call)
    }


@pytest.mark.parametrize("chokepoint", sorted(CHOKEPOINTS))
def test_every_chokepoint_calls_the_gate(chokepoint):
    path, function, gate = CHOKEPOINTS[chokepoint]
    assert gate in _function_calls(path, function)


def test_the_closure_validators_all_pass_the_chokepoint():
    tree = ast.parse((PACKAGE_ROOT / "proof/obligations/pair_closure_producers.py").read_text(encoding="utf-8"))
    validators = [
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name.startswith("validate_") and node.name.endswith("_candidate")
    ]
    assert len(validators) == 6
    for node in validators:
        calls = {getattr(call.func, "id", "") for call in ast.walk(node) if isinstance(call, ast.Call)}
        assert "_owner_free_identity_certificate" in calls, node.name


def test_every_memory_stage_requires_positional_parameter_locations():
    """左右の最終の memory 位置を組にする関数の呼び手は、全て G11 を先に呼ぶ。"""

    tree = ast.parse((PACKAGE_ROOT / "proof/call_effect/producer.py").read_text(encoding="utf-8"))
    callers = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.FunctionDef) or node.name == "_render_final_post_state_relation":
            continue
        calls = [call for call in ast.walk(node) if isinstance(call, ast.Call)]
        names = [getattr(call.func, "id", "") for call in calls]
        if "_render_final_post_state_relation" in names:
            callers.append(node.name)
            first_render = min(c.lineno for c in calls if getattr(c.func, "id", "") == "_render_final_post_state_relation")
            guards = [c.lineno for c in calls if getattr(c.func, "id", "") == "_require_positional_parameter_locations"]
            assert guards and min(guards) < first_render, node.name
    assert len(callers) == 3, callers


# ---------------------------------------------------------------------------
# U14: pair を閉じる経路
# ---------------------------------------------------------------------------


def _production_modules():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        if "tests" in path.relative_to(PACKAGE_ROOT).parts:
            continue
        yield path.relative_to(PACKAGE_ROOT).as_posix(), ast.parse(path.read_text(encoding="utf-8"))


def _enclosing(tree):
    owners = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for item in ast.walk(node):
                owners[id(item)] = node.name
    return owners


def _terminal_name(node):
    return getattr(node, "id", None) or getattr(node, "attr", None) or ""


def test_only_record_pair_closed_creates_and_records_a_pair_closure():
    offenders = []
    for path, tree in _production_modules():
        owners = _enclosing(tree)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
                continue
            receiver = node.func.value
            is_validated = node.func.attr == "validated" and _terminal_name(receiver) == "PairClosureEvidence"
            is_close = node.func.attr == "close" and "ledger" in _terminal_name(receiver)
            if (is_validated or is_close) and owners.get(id(node)) != "record_pair_closed":
                offenders.append((path, node.lineno, owners.get(id(node))))
    assert not offenders, offenders


def test_closure_evidence_is_constructed_and_stored_only_by_the_ledger():
    offenders = []
    for path, tree in _production_modules():
        if path == "proof/obligations/pair_disposition.py":
            continue
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and getattr(node.func, "id", "") == "PairClosureEvidence":
                offenders.append((path, node.lineno, "construct"))
            targets = node.targets if isinstance(node, ast.Assign) else [node.target] if isinstance(node, ast.AugAssign) else []
            for target in targets:
                if isinstance(target, ast.Subscript) and getattr(target.value, "attr", "") == "closures":
                    offenders.append((path, node.lineno, "store"))
            if (
                isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and getattr(node.func.value, "attr", "") == "closures"
                and node.func.attr in {"update", "setdefault", "__setitem__", "pop", "clear"}
            ):
                offenders.append((path, node.lineno, "mutate"))
    assert not offenders, offenders


def test_the_pairwise_eq_decision_counts_only_ledger_closures():
    """pairwise の EQ は ledger の ``counts()`` から決まる（局所の ``unsat_count`` では決めない）。"""

    source = (PACKAGE_ROOT / "proof/strategies/pairwise_services/orchestration.py").read_text(encoding="utf-8")
    decision = source.index("    ledger_counts = pair_ledger.counts()")
    tail = source[decision:source.index("elif unsat_count == total_pairs:", decision)]
    assert 'unsat_count = int(ledger_counts["unsat"])' in tail
