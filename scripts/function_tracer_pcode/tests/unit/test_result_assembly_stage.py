"""Phase 6b-5 (#82): 結果組み立て（E・F 段）と例外 → result（G 段の handler 本体）の抽出。
トップレベル try/except の catch scope と handler の種類・順序は check() に残る。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import patch

from scripts.function_tracer_pcode.checker import checker as checker_module
from scripts.function_tracer_pcode.checker import result_assembly as ra
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.core.render_smt import UnknownSmtExtensionWidthError, UnsupportedSmtOperatorError
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _check_fn():
    src = inspect.getsource(EquivalenceChecker.check)
    tree = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines()))
    return tree.body[0].body[0], src


def _top_try(fn):
    tries = [n for n in fn.body if isinstance(n, ast.Try)]
    assert len(tries) == 1
    return tries[0]


def _calls(node, name):
    return [n for n in ast.walk(node) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == name]


# ---- 静的: check() は result を直接構築せず、handler の種類・順序・catch scope は不変 -------------------

def test_check_no_longer_constructs_equivalence_result_directly():
    fn, src = _check_fn()
    assert "EquivalenceResult(" not in src
    assert not [n for n in ast.walk(fn) if isinstance(n, ast.Call) and ast.unparse(n.func) in {"EquivalenceResult", "create_error_result"}]
    # 私的付帯 3 つは check() から消え、段関数に移った
    for attr in ("_prepared_dispatch_frame", "_strategy_result", "_inconclusive_comparison_authority"):
        assert f".{attr} = " not in src  # 付帯の代入は check() に無い（build_prepared_dispatch_frame の名前は別物）
        assert f"equivalence_result.{attr} = " in inspect.getsource(ra.assemble_equivalence_result)


def test_top_level_try_except_handlers_keep_their_types_order_and_bodies():
    fn, _ = _check_fn()
    tr = _top_try(fn)
    assert len(tr.handlers) == 2 and not tr.orelse and not tr.finalbody
    assert ast.unparse(tr.handlers[0].type) == "(UnknownSmtExtensionWidthError, UnsupportedSmtOperatorError)"
    assert ast.unparse(tr.handlers[1].type) == "Exception"
    # handler 1: debug print → unsupported_smt_result を返す
    h1 = tr.handlers[0]
    assert len(_calls(h1, "unsupported_smt_result")) == 1
    assert isinstance(h1.body[-1], ast.Return) and getattr(h1.body[-1].value.func, "id", "") == "unsupported_smt_result"
    # handler 2: debug print / traceback → ReturnAbiAuthorityInvalid なら canonical helper、それ以外は self._create_error_result
    h2 = tr.handlers[1]
    ifs = [n for n in h2.body if isinstance(n, ast.If)]
    # if self.debug: traceback（従来どおり）と isinstance 分岐の 2 つ、この順
    assert [ast.unparse(n.test) for n in ifs] == ["self.debug", "isinstance(e, ReturnAbiAuthorityInvalid)"] and not ifs[1].orelse
    ifs = ifs[1:]
    assert isinstance(ifs[0].body[-1], ast.Return) and getattr(ifs[0].body[-1].value.func, "id", "") == "canonical_abi_error_result"
    assert isinstance(h2.body[-1], ast.Return) and ast.unparse(h2.body[-1].value.func) == "self._create_error_result"


def test_all_stage_calls_stay_inside_the_top_level_try_body():
    fn, _ = _check_fn()
    tr = _top_try(fn)
    body_lines = range(tr.body[0].lineno, tr.handlers[0].lineno)
    for name in ("build_branch_check_context", "prepare_preflight_projection", "build_prepared_dispatch_frame",
                 "prepare_strategy_runtime", "run_strategy_branch", "run_legacy_strategy", "refine_unknown_reasons",
                 "prepare_recurrence_promotion", "complete_recurrence_promotion_signals", "assemble_equivalence_result"):
        calls = _calls(fn, name)
        assert len(calls) == 1, name
        assert calls[0].lineno in body_lines, name
    # 通常経路の return は assemble_equivalence_result の戻り値そのもの（try 本体の最後）
    last = tr.body[-1]
    assert isinstance(last, ast.Return) and getattr(last.value.func, "id", "") == "assemble_equivalence_result"
    kw = {k.arg for k in last.value.keywords}
    assert {"ctx", "dispatch_frame", "preflight_gate_delta_diagnostic", "call_effect_shadow_manifest", "start_time",
            "type_fix_result", "retry_count", "original_signature1", "original_signature2", "rewrite_info", "debug",
            "deterministic_analysis_identity", "format_counterexample", "completed_recovery_proof_payload",
            "reason_completion_applicability_contexts", "recurrence_promotion_result_receipt"} == kw


# ---- 動的: catch scope（どの段の例外がどの handler に届くか） ------------------------------------------

def _checker():
    return EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)


def test_unsupported_smt_error_raised_in_the_assembly_stage_is_still_caught_by_the_first_handler():
    analysis = create_mock_analysis("f", [])
    checker = _checker()
    err = UnknownSmtExtensionWidthError(operator="INT_ZEXT", operand_bits=32)
    with patch.object(checker_module, "assemble_equivalence_result", side_effect=err):
        result = checker.check(analysis, analysis, "b1", "b2")
    assert result.is_equivalent is None and result.error_message is None
    assert result.pairwise_debug_stats == {"unknown_smt_extension_width": 1}
    assert [r.reason_id for r in result.unknown_reasons] == ["expression_semantics_unsupported"]
    assert result.unknown_reasons[0].evidence_refs == ("unknown_smt_extension_width",)
    assert result.binary1_name == "b1" and result.function1_name == analysis.function_name


def test_unsupported_operator_error_raised_before_the_strategy_maps_to_the_operator_kind():
    analysis = create_mock_analysis("f", [])
    checker = _checker()
    checker._call_effect_shadow_manifest = lambda *a, **k: (_ for _ in ()).throw(UnsupportedSmtOperatorError(operator="FLOAT_ADD", reason="float", operand_bits=64))
    result = checker.check(analysis, analysis)
    assert result.pairwise_debug_stats == {"unsupported_smt_operator": 1}
    assert result.unknown_reasons[0].evidence_refs == ("unsupported_smt_operator",)


def test_return_abi_authority_invalid_maps_to_the_canonical_error_kind():
    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import ReturnAbiAuthorityInvalid
    analysis = create_mock_analysis("f", [])
    checker = _checker()
    exc = ReturnAbiAuthorityInvalid("bad_slot", malformed_slots=("r0",), detail="d")
    with patch.object(checker_module, "assemble_equivalence_result", side_effect=exc):
        result = checker.check(analysis, analysis)
    assert result.is_equivalent is None
    assert result.error_message == "return_abi_authority_invalid"
    assert result.failure_status == "return_abi_authority_invalid"
    assert result.failure_message == str(exc)


def test_other_exceptions_still_go_through_the_instance_create_error_result_seam():
    analysis = create_mock_analysis("f", [])
    checker = _checker()
    seen = {}

    def fake_error_result(a1, a2, b1, b2, message, start_time, type_fix_result, retry_count, sig1, sig2):
        seen.update(message=message, b1=b1)
        return "ERROR_RESULT"

    checker._create_error_result = fake_error_result
    with patch.object(checker_module, "assemble_equivalence_result", side_effect=RuntimeError("assembly boom")):
        assert checker.check(analysis, analysis, "L", "R") == "ERROR_RESULT"
    assert seen == {"message": "assembly boom", "b1": "L"}


# ---- 段関数の単体 ----------------------------------------------------------------------------------

def test_unsupported_smt_result_shape_and_diagnostic_kind():
    analysis = create_mock_analysis("f", [])
    err = UnsupportedSmtOperatorError(operator="FLOAT_ADD", reason="float", operand_bits=64)
    result = ra.unsupported_smt_result(err, analysis1=analysis, analysis2=analysis, binary1_name="a", binary2_name="b",
                                       start_time=0.0, type_fix_result=None, retry_count=2, original_signature1=None, original_signature2=None)
    assert isinstance(result, EquivalenceResult) and result.is_equivalent is None and result.retry_count == 2
    assert result.pairwise_debug_stats == {"unsupported_smt_operator": 1} and result.constrained_fragments == []
    reason = result.unknown_reasons[0]
    assert reason.reason_id == "expression_semantics_unsupported" and reason.evidence_refs == ("unsupported_smt_operator",)
    assert ra.unsupported_smt_diagnostic_kind(UnknownSmtExtensionWidthError(operator="INT_ZEXT", operand_bits=8)) == "unknown_smt_extension_width"


def test_assemble_result_attaches_private_capabilities_and_terminal_provenance_in_order():
    analysis = create_mock_analysis("f", [])
    from scripts.function_tracer_pcode.checker.branch_context import BranchCheckContext
    from scripts.function_tracer_pcode.proof.call_effect.preflight import CallProofDecisionMode
    ctx = BranchCheckContext(strategy=object(), replan_plan=None, generation=3, comparison_session_id="S", branch_id="B",
                             decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION, production_branch_authority_lease=None)
    sr = SimpleNamespace(is_equivalent=False, counterexample_raw={"x": 1}, return_var1=None, return_var2="r2", smt_formula="(f)",
                         solver_results=None, constrained_fragments=[], total_pairs=2, unsat_pairs=1, sat_pairs=1, unknown_pairs=0, error_pairs=0,
                         pairwise_debug_stats={}, unknown_reasons=[], error_message=None, error_kind=None, sat_pair_info=None,
                         normalization_rules=None, completed_recovery_proof_evidence=())
    events = []
    result = ra.assemble_equivalence_result(
        sr, analysis, analysis, "L", "R", ctx=ctx, dispatch_frame=None, preflight_gate_delta_diagnostic={"d": 1},
        call_effect_shadow_manifest={"m": 1}, start_time=0.0, type_fix_result=None, retry_count=0,
        original_signature1=None, original_signature2=None, rewrite_info=None, debug=False,
        deterministic_analysis_identity=lambda strategy, a: events.append(("identity", strategy)) or "ID",
        format_counterexample=lambda raw, a1, a2, v1, v2: events.append(("cex", raw, v1, v2)) or "CEX",
        completed_recovery_proof_payload=lambda a1, a2, b1, b2, *, extra_records: events.append(("proofs", b1, b2, extra_records)) or ["P"],
        reason_completion_applicability_contexts=lambda proofs, a1, a2: events.append(("contexts", proofs)) or ["C"],
        recurrence_promotion_result_receipt=lambda s: events.append(("receipt",)) or "RCPT",
    )
    assert [e[0] for e in events] == ["identity", "identity", "cex", "proofs", "contexts", "receipt"]
    assert events[0][1] is ctx.strategy and events[2][1:] == ({"x": 1}, "return_1", "r2") and events[3][1:] == ("L", "R", ())
    assert events[4][1] == ["P"]
    assert result.counterexample == "CEX" and result.completed_recovery_proof_evidence == ["P"]
    assert result.reason_completion_applicability_contexts == ["C"] and result.recurrence_promotion_receipt == "RCPT"
    assert result.pairwise_stats == {"total_pairs": 2, "unsat_pairs": 1, "sat_pairs": 1, "unknown_pairs": 0, "error_pairs": 0}
    prov = result.call_proof_terminal_provenance
    assert (prov["comparison_session_id"], prov["terminal_branch_id"], prov["projection_generation"]) == ("S", "B", 3)
    assert prov["decision_owner_mode"] == "preflight_projection" and prov["terminal_outcome"] == "NOT_EQ"
    assert prov["dispatch_cleanup_complete"] is True and prov["preflight_gate_delta_diagnostic"] == {"d": 1}
    assert result._prepared_dispatch_frame is None and result._strategy_result is sr and result._inconclusive_comparison_authority is None
    assert result.function1_identity == "ID" and result.call_effect_shadow_manifest == {"m": 1}
