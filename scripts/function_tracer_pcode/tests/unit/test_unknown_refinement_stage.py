"""Phase 6b-3 (#82): UNKNOWN reason refinement 段の抽出。
recurrence proposal blocker → call-effect specialization → root blocker identity の逐次順序と、
各段の出力が次段へ渡ることを固定する。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import patch

from scripts.function_tracer_pcode.checker import unknown_refinement as ur
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


class _RecordingResult:
    """unknown_reasons への書き込みを順に記録する strategy_result の代替。"""

    def __init__(self, initial):
        self.writes = []
        self._reasons = initial

    @property
    def unknown_reasons(self):
        return self._reasons

    @unknown_reasons.setter
    def unknown_reasons(self, value):
        self.writes.append(value)
        self._reasons = value


def _run(events, initial=("r0",)):
    result = _RecordingResult(list(initial))
    identity = object()
    stage1 = ["r0", "recurrence_blocker"]
    stage2 = ["specialized"]
    stage3 = ["with_identity"]

    def identity_fn(a1, a2, manifest):
        events.append(("identity", a1, a2, manifest))
        return identity

    def recurrence(sr, a1, a2, *, branch_id):
        events.append(("recurrence", sr, a1, a2, branch_id, list(sr.unknown_reasons)))
        return stage1

    def specialize(reasons, manifest, *, comparison_identity):
        events.append(("specialize", reasons, manifest, comparison_identity))
        return stage2

    def root_identity(reasons, comparison_identity):
        events.append(("root_identity", reasons, comparison_identity))
        return stage3

    outcome = ur.refine_unknown_reasons(
        result, "a1", "a2", {"m": 1}, branch_id="B",
        call_effect_comparison_identity=identity_fn,
        attach_recurrence_proposal_blockers=recurrence,
        specialize_call_effect_unknown_reasons=specialize,
        attach_root_blocker_identities=root_identity,
    )
    return result, identity, stage1, stage2, stage3, outcome


def test_stages_run_in_the_fixed_order_identity_recurrence_specialize_root_identity():
    events = []
    _run(events)
    assert [e[0] for e in events] == ["identity", "recurrence", "specialize", "root_identity"]


def test_each_stage_output_is_passed_to_the_next_and_written_back_in_order():
    events = []
    result, identity, stage1, stage2, stage3, outcome = _run(events)
    # identity は manifest と両 analysis から 1 回だけ計算され、2 段目・3 段目に同じ object が渡る
    assert events[0][1:] == ("a1", "a2", {"m": 1})
    assert events[2][3] is identity and events[3][2] is identity
    # recurrence 段は strategy_result 自体と branch_id を受け取り、その時点の reasons は初期値
    assert events[1][1] is result and events[1][4] == "B" and events[1][5] == ["r0"]
    # specialization は recurrence 段の出力を list() コピーで受け取る（同一 object ではない、内容は同じ）
    assert events[2][1] == stage1 and events[2][1] is not stage1 and events[2][2] == {"m": 1}
    # root identity は specialization の出力そのものを受け取る
    assert events[3][1] is stage2
    # strategy_result.unknown_reasons は 3 回、各段の出力で順に書き戻される
    assert result.writes == [stage1, stage2, stage3]
    assert result.writes[0] is stage1 and result.writes[1] is stage2 and result.writes[2] is stage3
    assert result.unknown_reasons is stage3
    assert outcome.comparison_identity is identity
    assert outcome.reasons_after_recurrence_blockers is stage1
    assert outcome.reasons_after_call_effect_specialization is stage2
    assert outcome.final_reasons is stage3


def test_specialization_receives_an_empty_list_when_recurrence_stage_returns_none():
    """旧実装の list(getattr(..., ()) or ()) を維持する。"""
    result = _RecordingResult(["r0"])
    seen = {}
    ur.refine_unknown_reasons(
        result, "a1", "a2", {}, branch_id="B",
        call_effect_comparison_identity=lambda *a: "id",
        attach_recurrence_proposal_blockers=lambda *a, **k: None,
        specialize_call_effect_unknown_reasons=lambda reasons, m, *, comparison_identity: seen.setdefault("reasons", reasons) or ["x"],
        attach_root_blocker_identities=lambda reasons, identity: reasons,
    )
    assert seen["reasons"] == [] and result.writes[0] is None


def test_check_calls_the_stage_once_and_no_longer_calls_the_four_mixins_directly():
    src = inspect.getsource(EquivalenceChecker.check)
    tree = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines()))
    fn = tree.body[0].body[0]
    calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == "refine_unknown_reasons"]
    assert len(calls) == 1
    kw = {k.arg: ast.unparse(k.value) for k in calls[0].keywords}
    assert kw == {
        "branch_id": "branch_id",
        "call_effect_comparison_identity": "self._call_effect_comparison_identity",
        "attach_recurrence_proposal_blockers": "self._attach_recurrence_proposal_blockers",
        "specialize_call_effect_unknown_reasons": "self._specialize_call_effect_unknown_reasons",
        "attach_root_blocker_identities": "self._attach_root_blocker_identities",
    }
    direct = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
              and n.func.attr in {"_call_effect_comparison_identity", "_attach_recurrence_proposal_blockers",
                                  "_specialize_call_effect_unknown_reasons", "_attach_root_blocker_identities"}]
    assert direct == []
    # check() 自身は unknown_reasons を書かない（書き戻しは段関数内）
    writes = [n for n in ast.walk(fn) if isinstance(n, ast.Assign)
              and any(isinstance(t, ast.Attribute) and t.attr == "unknown_reasons" for t in n.targets)]
    assert writes == []
    # refine は strategy 実行（run_strategy_branch）の後、recurrence promotion authority の前
    run_line = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == "run_strategy_branch"][0].lineno
    # 6b-4 以降、recurrence promotion authority の判定は prepare_recurrence_promotion(...) 経由
    promo_line = [n for n in ast.walk(fn) if isinstance(n, ast.Call)
                  and getattr(n.func, "id", "") == "prepare_recurrence_promotion"][0].lineno
    assert run_line < calls[0].lineno < promo_line


def test_instance_patch_of_a_mixin_method_is_still_honored_through_check():
    """check() は mixin を call 時に self から解決するので、instance patch seam は従来どおり効く。"""
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    seen = []

    def spy_specialize(reasons, manifest, *, comparison_identity):
        seen.append((list(reasons), comparison_identity))
        return list(reasons) + ["patched_marker"]

    checker._specialize_call_effect_unknown_reasons = spy_specialize
    with patch.object(checker, "_attach_root_blocker_identities", side_effect=lambda reasons, identity: (seen.append(("root", list(reasons))) or reasons)):
        result = checker.check(analysis, analysis)
    assert result.error_message is None
    assert len(seen) == 2 and seen[0][1] is not None
    # 2 段目の出力（marker 付き）がそのまま 3 段目へ渡っている。最終 result の reasons は後段（E/F）で
    # 正規化されるため、ここでは段間の受け渡しだけを見る。
    assert seen[1] == ("root", seen[0][0] + ["patched_marker"])
