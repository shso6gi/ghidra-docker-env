from scripts.function_tracer_pcode.validation.refactor_contract import (
    PUBLIC_SYMBOLS,
    PRODUCTION_HOOKS,
    capture_contract,
    dependency_snapshot,
)
from scripts.function_tracer_pcode.validation.refactor_equivalence import (
    attempt_final_smt_events_from_records,
    capture_refactor_surface_from_logs,
    canonical_json_hash,
    canonical_smt_surface,
    compare_refactor_surfaces,
)
from scripts.function_tracer_pcode.validation.result_summary import (
    read_validation_log_record,
)


def test_refactor_public_symbols_and_hooks_are_importable():
    contract = capture_contract()
    assert len(contract["symbols"]) == sum(len(names) for names in PUBLIC_SYMBOLS.values())
    assert len(contract["hooks"]) == sum(len(names) for names in PRODUCTION_HOOKS.values())
    assert isinstance(contract["tracked_dirty"], bool)


def test_dependency_snapshot_has_deterministic_edges_and_cycles():
    first = dependency_snapshot()
    second = dependency_snapshot()
    assert first == second


def test_canonical_json_ignores_only_declared_volatile_fields():
    before = {"timestamp": "one", "decision": "EQ", "nested": {"value": 1}}
    after = {"timestamp": "two", "decision": "EQ", "nested": {"value": 1}}
    changed = {"timestamp": "two", "decision": "NOT_EQ", "nested": {"value": 1}}
    assert canonical_json_hash(before) == canonical_json_hash(after)
    assert canonical_json_hash(before) != canonical_json_hash(changed)


def test_canonical_json_preserves_semantic_program_addresses():
    assert canonical_json_hash({"target": "ram:0x00401000"}) != canonical_json_hash(
        {"target": "ram:0x00402000"}
    )


def test_canonical_json_ignores_ghidra_program_object_id_but_keeps_function_entry():
    first_import = {"key": ["function", 3740770641074218464, 0x401000]}
    second_import = {"key": ["function", 3740771657573150464, 0x401000]}
    different_entry = {"key": ["function", 3740771657573150464, 0x402000]}

    assert canonical_json_hash(first_import) == canonical_json_hash(second_import)
    assert canonical_json_hash(first_import) != canonical_json_hash(different_entry)

    first_parameter = {"key": ["parameter", 3740770641074218464, 0x401000, 0]}
    second_parameter = {"key": ["parameter", 3740771657573150464, 0x401000, 0]}
    different_parameter_entry = {
        "key": ["parameter", 3740771657573150464, 0x402000, 0]
    }
    assert canonical_json_hash(first_parameter) == canonical_json_hash(second_parameter)
    assert canonical_json_hash(first_parameter) != canonical_json_hash(
        different_parameter_entry
    )


def test_canonical_json_ignores_only_python_object_repr_identity():
    first = {"value": "<example.Widget object at 0x12345678>"}
    second = {"value": "<example.Widget object at 0x87654321>"}
    assert canonical_json_hash(first) == canonical_json_hash(second)


def test_canonical_package_imports_from_outside_repository(tmp_path):
    repo_root = Path(__file__).resolve().parents[4]
    environment = dict(os.environ, PYTHONPATH=str(repo_root / "scripts"))
    subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import function_tracer_pcode; "
                "from function_tracer_pcode.analysis.effect_models import EffectSummary; "
                "from function_tracer_pcode.analysis.effect_services.location "
                "import implementation; "
                "assert implementation('canonicalize_location') is not None"
            ),
        ],
        cwd=tmp_path,
        env=environment,
        check=True,
    )


def test_compatibility_package_imports_from_outside_repository(tmp_path):
    repo_root = Path(__file__).resolve().parents[4]
    environment = dict(os.environ, PYTHONPATH=str(repo_root))
    subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import scripts.function_tracer_pcode; "
                "from scripts.function_tracer_pcode.analysis.effect_models "
                "import EffectSummary"
            ),
        ],
        cwd=tmp_path,
        env=environment,
        check=True,
    )


def test_smt_structural_hash_normalizes_nonsemantic_command_order():
    left = """
    (declare-const x (_ BitVec 32))
    (declare-const y (_ BitVec 32))
    (assert (= x y))
    (check-sat)
    """
    right = """
    (declare-const y (_ BitVec 32))
    (declare-const x (_ BitVec 32))
    (assert (= y x))
    (check-sat)
    """
    left_surface = canonical_smt_surface(left)
    right_surface = canonical_smt_surface(right)
    assert left_surface["raw_stable_hash"] != right_surface["raw_stable_hash"]
    assert left_surface["structural_exact_hash"] == right_surface["structural_exact_hash"]


def test_smt_controlled_alpha_requires_object_binding():
    left = "(declare-const tmp_1 (_ BitVec 32)) (assert (= tmp_1 #x00000001))"
    right = "(declare-const tmp_2 (_ BitVec 32)) (assert (= tmp_2 #x00000001))"
    unbound_left = canonical_smt_surface(left)
    unbound_right = canonical_smt_surface(right)
    assert unbound_left["controlled_alpha_hash"] != unbound_right["controlled_alpha_hash"]

    bound_left = canonical_smt_surface(
        left, query_event={"symbol_bindings": {"tmp_1": ["parameter", 0]}}
    )
    bound_right = canonical_smt_surface(
        right, query_event={"symbol_bindings": {"tmp_2": ["parameter", 0]}}
    )
    assert bound_left["controlled_alpha_hash"] == bound_right["controlled_alpha_hash"]
    assert bound_left["structural_exact_hash"] != bound_right["structural_exact_hash"]


def test_refactor_surface_comparison_reports_the_changed_lane():
    before = {"schema_version": 1, "validation": {}, "records": [], "queries": []}
    after = {"schema_version": 1, "validation": {}, "records": [], "queries": [{"status": "sat"}]}
    assert compare_refactor_surfaces(before, after) == ("queries_changed",)


def test_real_log_surface_captures_ordered_query_evidence(tmp_path):
    log = tmp_path / "sample_B1_B2.log"
    log.write_text(
        'Result: EQUIVALENT\n'
        '=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n'
        '{"function1_name":"sample","is_equivalent":true,"debug_trace":{"attempts":['
        '{"attempt_id":0,"phase":"P0","final_smt":"(check-sat)",'
        '"solver_results":{"first_definitive":{"status":"UNSAT"}}}]}}\n'
        '=== EQUIVALENCE_RESULT_JSON_END ===\n',
        encoding="utf-8",
    )
    surface = capture_refactor_surface_from_logs((log,))
    assert surface["records"][0]["final_result"] == "EQ"
    assert surface["queries"][0]["status"] == "UNSAT"
    assert surface["queries"][0]["smt"]["major_structure_hash"]


def test_attempt_surface_extractor_is_explicitly_attempt_level(tmp_path):
    log = tmp_path / "sample_B1_B2.log"
    log.write_text(
        '=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n'
        '{"is_equivalent":true,"debug_trace":{"attempts":['
        '{"attempt_id":0,"final_smt":"(check-sat)"},'
        '{"attempt_id":1,"final_smt":"(check-sat)"}]}}\n'
        '=== EQUIVALENCE_RESULT_JSON_END ===\n',
        encoding="utf-8",
    )
    record = read_validation_log_record(log)
    events = attempt_final_smt_events_from_records((record,))
    assert [event["attempt_index"] for event in events] == [0, 1]


def test_analysis_session_preserves_nested_context_identity_and_restores_values():
    from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer

    analyzer = ReturnAnalyzer.__new__(ReturnAnalyzer)
    analyzer.debug = False
    analyzer._current_parameters = [{"name": "outer"}]
    analyzer._current_deferred_calls = {("outer",): object()}
    session = analyzer._analysis_session
    outer_calls = analyzer._current_deferred_calls

    with analyzer._analysis_context([{"name": "inner"}], None):
        assert analyzer._analysis_session is session
        assert analyzer._current_parameters == [{"name": "inner"}]
        assert analyzer._current_deferred_calls == {}

    assert analyzer._analysis_session is session
    assert analyzer._current_parameters == [{"name": "outer"}]
    assert analyzer._current_deferred_calls is outer_calls
import os
from pathlib import Path
import subprocess
import sys
