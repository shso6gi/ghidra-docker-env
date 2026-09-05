"""Phase 6b-4 (#82): recurrence promotion 段の抽出。
(1) authority 判定 → (2) promote → (3) _last_recurrence_promotion_attempt 書き込み → (4) completion signal
→ (5) _obligation_runtime_session → (6) _active_recurrence_promotion_authority → (7) 再帰 check → (8) finally 削除
の時間的順序と facade write の位置を固定する。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import patch

from scripts.function_tracer_pcode.checker import checker as checker_module
from scripts.function_tracer_pcode.checker import recurrence_promotion as rp
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.proof.recurrence_promotion import PairPromotionState
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

SIGNALS = "scripts.function_tracer_pcode.authority.lifecycle.production_signals"
DOMAIN = "scripts.function_tracer_pcode.authority.domains.loop_recurrence"


def _attempt(state, left=None, right=None, failure=None):
    return SimpleNamespace(state=state, left=left, right=right, failure=failure)


def _side(proposal):
    return SimpleNamespace(proposal=proposal)


# ---- prepare_recurrence_promotion -------------------------------------------------------------

def test_prepare_returns_none_without_calling_promote_when_no_authority():
    calls = []
    with patch.object(rp, "promote_recurrence_pair", side_effect=lambda *a: calls.append(a)):
        prep = rp.prepare_recurrence_promotion("sr", "a1", "a2", comparison_session_id="S", branch_id="B",
                                               recurrence_promotion_authority=lambda sr, *, comparison_session_id, branch_id: None)
    assert prep is None and calls == []


def test_prepare_passes_strategy_result_session_and_branch_then_promotes_with_the_authority():
    seen = {}

    def authority_fn(sr, *, comparison_session_id, branch_id):
        seen["authority_args"] = (sr, comparison_session_id, branch_id)
        return "AUTH"

    with patch.object(rp, "promote_recurrence_pair", side_effect=lambda a1, a2, auth: (seen.setdefault("promote", (a1, a2, auth)) and ("p1", "p2", "rt", "att"))):
        prep = rp.prepare_recurrence_promotion("sr", "a1", "a2", comparison_session_id="S", branch_id="B",
                                               recurrence_promotion_authority=authority_fn)
    assert seen["authority_args"] == ("sr", "S", "B") and seen["promote"] == ("a1", "a2", "AUTH")
    assert (prep.authority, prep.promoted1, prep.promoted2, prep.recurrence_runtime, prep.attempt) == ("AUTH", "p1", "p2", "rt", "att")


# ---- complete_recurrence_promotion_signals ----------------------------------------------------

def test_aborted_attempt_only_prints_debug_and_does_not_recurse():
    msgs = []
    with patch(SIGNALS + ".emit_loop_recurrence_signal") as emit:
        assert rp.complete_recurrence_promotion_signals(_attempt(PairPromotionState.ABORTED, failure="why"), debug_print=msgs.append) is False
    assert msgs == ["Recurrence promotion declined: why"] and not emit.called


def test_composed_without_proposals_neither_signals_nor_recurses():
    with patch(SIGNALS + ".emit_loop_recurrence_signal") as emit:
        assert rp.complete_recurrence_promotion_signals(_attempt(PairPromotionState.COMPOSED, _side(None), None), debug_print=lambda m: None) is False
    assert not emit.called


def test_composed_with_proposals_emits_one_signal_per_side_with_a_proposal_and_recurses():
    left, right = _side("L"), _side(None)
    emitted = []
    with patch(SIGNALS + ".emit_loop_recurrence_signal", side_effect=lambda sig, *, producer_site_manifest_id: emitted.append((sig, producer_site_manifest_id))), \
         patch(DOMAIN + ".RecurrenceValidationCompletionSignal") as sig_cls:
        sig_cls.from_side_promotion.side_effect = lambda side: ("SIG", side)
        assert rp.complete_recurrence_promotion_signals(_attempt(PairPromotionState.COMPOSED, left, right), debug_print=lambda m: None) is True
    assert emitted == [(("SIG", left), "checker-recurrence-validation-completed")]


def test_signal_failure_is_recorded_as_shadow_error_and_still_recurses():
    recorded = []
    with patch(SIGNALS + ".emit_loop_recurrence_signal", side_effect=RuntimeError("bus down")), \
         patch(SIGNALS + ".record_production_pilot_shadow_error", side_effect=recorded.append), \
         patch(DOMAIN + ".RecurrenceValidationCompletionSignal") as sig_cls:
        sig_cls.from_side_promotion.side_effect = lambda side: "SIG"
        assert rp.complete_recurrence_promotion_signals(_attempt(PairPromotionState.COMPOSED, _side("L"), _side("R")), debug_print=lambda m: None) is True
    assert [str(e) for e in recorded] == ["bus down", "bus down"]


# ---- check(): facade write の位置（静的） --------------------------------------------------------

def _check_fn():
    src = inspect.getsource(EquivalenceChecker.check)
    tree = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines()))
    return tree.body[0].body[0]


def _assign_lines(fn, attr):
    return [n.lineno for n in ast.walk(fn) if isinstance(n, ast.Assign)
            and any(isinstance(t, ast.Attribute) and t.attr == attr for t in n.targets)]


def _call_line(fn, name):
    calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == name]
    assert len(calls) == 1, name
    return calls[0].lineno


def test_check_keeps_facade_writes_and_recursion_in_the_fixed_order():
    fn = _check_fn()
    prepare = _call_line(fn, "prepare_recurrence_promotion")
    attempt_write = _assign_lines(fn, "_last_recurrence_promotion_attempt")
    signals = _call_line(fn, "complete_recurrence_promotion_signals")
    runtime_writes = _assign_lines(fn, "_obligation_runtime_session")
    authority_write = _assign_lines(fn, "_active_recurrence_promotion_authority")
    assert len(attempt_write) == 1 and len(authority_write) == 1
    # (5) の runtime write は D 段の 1 箇所（もう 1 箇所は B 段の store_on_facade）
    d_runtime = [l for l in runtime_writes if l > signals]
    assert len(d_runtime) == 1 and len(runtime_writes) == 2
    # 再帰 self.check(...) は facade（check() 本体）に残り、try の finally で active authority を削除する
    recursive = [n for n in ast.walk(fn) if isinstance(n, ast.Try)
                 and any(isinstance(d, ast.Delete) and any(isinstance(t, ast.Attribute) and t.attr == "_active_recurrence_promotion_authority" for t in d.targets) for d in n.finalbody)]
    assert len(recursive) == 1
    ret = [n for n in ast.walk(recursive[0]) if isinstance(n, ast.Return) and isinstance(n.value, ast.Call)
           and isinstance(n.value.func, ast.Attribute) and n.value.func.attr == "check" and ast.unparse(n.value.func.value) == "self"]
    assert len(ret) == 1
    # 再帰呼び出しは promoted pair を位置引数に、元の strategy を force_strategy に渡す
    assert [ast.unparse(a) for a in ret[0].value.args[:2]] == ["promotion.promoted1", "promotion.promoted2"]
    assert {k.arg: ast.unparse(k.value) for k in ret[0].value.keywords}["force_strategy"] == "strategy"
    assert prepare < attempt_write[0] < signals < d_runtime[0] < authority_write[0] < ret[0].lineno < recursive[0].finalbody[0].lineno
    # (3) は (4) の条件分岐の外（signals の if の前）にある: attempt write は if の test より前の行
    ifs = [n for n in ast.walk(fn) if isinstance(n, ast.If) and "complete_recurrence_promotion_signals" in ast.unparse(n.test)]
    assert len(ifs) == 1 and attempt_write[0] < ifs[0].lineno and not ifs[0].orelse
    # 段関数に setter callback を渡していない / promote は check() から消えている
    src = inspect.getsource(EquivalenceChecker.check)
    assert "promote_recurrence_pair" not in src and "PairPromotionState" not in src and "setattr" not in src


# ---- check(): 動的順序 ----------------------------------------------------------------------------

class _Observing(EquivalenceChecker):
    """facade write と再帰 check を順に記録する。"""

    def __init__(self, *a, **k):
        object.__setattr__(self, "events", [])
        super().__init__(*a, **k)

    def __setattr__(self, name, value):
        if name in {"_last_recurrence_promotion_attempt", "_obligation_runtime_session", "_active_recurrence_promotion_authority"} and hasattr(self, "events"):
            self.events.append(("set", name, value))
        object.__setattr__(self, name, value)

    def __delattr__(self, name):
        if name == "_active_recurrence_promotion_authority":
            self.events.append(("del", name))
        object.__delattr__(self, name)

    def check(self, analysis1, analysis2, *a, **k):
        if getattr(self, "_active_recurrence_promotion_authority", None) is not None:
            self.events.append(("recursive_check", analysis1, analysis2, k.get("force_strategy"),
                                self._obligation_runtime_session, self._active_recurrence_promotion_authority))
            return "NESTED_RESULT"
        return super().check(analysis1, analysis2, *a, **k)


def test_check_dynamic_order_attempt_signals_runtime_authority_recursion_cleanup():
    analysis = create_mock_analysis("f", [])
    checker = _Observing(strategy="pairwise", timeout=5, monolithic_timeout=5)
    attempt = _attempt(PairPromotionState.COMPOSED, _side("L"), None)
    authority = object()
    checker._recurrence_promotion_authority = lambda sr, *, comparison_session_id, branch_id: authority
    with patch.object(rp, "promote_recurrence_pair", return_value=("P1", "P2", "RT", attempt)), \
         patch.object(checker_module, "complete_recurrence_promotion_signals",
                      side_effect=lambda att, *, debug_print: checker.events.append(("signals", att)) or True):
        result = checker.check(analysis, analysis)
    assert result == "NESTED_RESULT"
    events = [e for e in checker.events if not (e[0] == "set" and e[1] == "_obligation_runtime_session" and e[2] != "RT")]
    assert [e[:2] if e[0] != "signals" else e for e in events] == [
        ("set", "_last_recurrence_promotion_attempt"),
        ("signals", attempt),
        ("set", "_obligation_runtime_session"),
        ("set", "_active_recurrence_promotion_authority"),
        ("recursive_check", "P1"),
        ("del", "_active_recurrence_promotion_authority"),
    ]
    assert events[0][2] is attempt and events[2][2] == "RT" and events[3][2] is authority
    # 再帰 check は promoted pair・元の strategy（force_strategy）・(5)(6) で書いた runtime / authority を見る
    assert events[4] == ("recursive_check", "P1", "P2", checker.check_strategy, "RT", authority)
    assert events[4][3] is checker.check_strategy
    assert not hasattr(checker, "_active_recurrence_promotion_authority")
    assert checker._last_recurrence_promotion_attempt is attempt


def test_check_dynamic_no_recursion_when_signals_stage_declines():
    analysis = create_mock_analysis("f", [])
    checker = _Observing(strategy="pairwise", timeout=5, monolithic_timeout=5)
    attempt = _attempt(PairPromotionState.ABORTED, failure="no")
    checker._recurrence_promotion_authority = lambda sr, *, comparison_session_id, branch_id: object()
    with patch.object(rp, "promote_recurrence_pair", return_value=("P1", "P2", "RT", attempt)):
        result = checker.check(analysis, analysis)
    names = [e[1] for e in checker.events if e[0] == "set"]
    assert "_last_recurrence_promotion_attempt" in names and "_active_recurrence_promotion_authority" not in names
    assert not any(e[0] == "recursive_check" for e in checker.events)
    assert result != "NESTED_RESULT" and result.error_message is None and checker._obligation_runtime_session != "RT"
