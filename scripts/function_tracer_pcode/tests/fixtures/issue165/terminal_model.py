# -*- coding: utf-8 -*-
"""Issue #165: 終端の状態機械を、durable な公開境界ごとの crash で機械検証する model。

production の ``next_step``（``authority/process/terminal_recovery.py``）を
そのまま使い、model 側は「store に何の file があるか」だけを持つ。

* **状態**（``ModelState``）: store に durable にある物件の抽象（D / E / A、
  pending-active、live chain とその state、history、timeout / error の
  member、canonical resolved receipt、envelope、projection）。
* **操作**: production の公開操作を、**1 回の durable な公開（write /
  rename / unlink）ごと**の列として写す（``OPERATIONS`` の各関数が列を返す）。
  列は production の store / command と同じ順序（``README.md`` の対応表）。
  crash は列の任意の位置で起き、restart は同じ ``drive`` をやり直す。
* **到達集合**: child の各公開の直後で child が終わる（自然終了 / deadline）
  すべての scenario × mode × supervisor の各公開の直後の crash を、
  restart の繰り返しを含めて閉包まで辿る。reachable な状態を
  「well-formed でない」として除外しない。
* **oracle**（期待終端）は ``next_step`` からは作らない。scenario の事実
  （child がどこまで進んだか・どう終わったか・E が durable になったか・
  mode・envelope）だけから ``expected_terminal`` が決める。

検査（``check``）:

1. すべての reachable 状態から crash 無しで drive すると、その scenario の
   oracle の終端（INVALID は code まで）に着く。
2. cycle 0（drive 中に同じ状態へ戻らない）、各 progress 操作が状態を変える。
3. ``next_step`` が例外を出さない（unhandled 0）。INVALID は code と detail
   を持つ。
4. malformed / tampered（別集合）: reachable 状態を改ざんした状態では、
   最初の判定が INVALID（書込みより前に拒否）。対照として「無関係な古い
   history を足しただけ」の状態は終端が変わらない。

    python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue165.terminal_model
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
import json
from typing import Callable, Iterable, Optional

from scripts.function_tracer_pcode.authority.process import store_layout as layout
from scripts.function_tracer_pcode.authority.process.terminal_evidence import (
    ANCHOR_CHAIN,
    ANCHOR_NONE,
    ANCHOR_PENDING_ACTIVE,
    CheckpointAnchor,
)
from scripts.function_tracer_pcode.authority.process import terminal_recovery as tr
from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
    CheckpointState,
    ErrorStage,
)
from scripts.function_tracer_pcode.authority.process.checkpoint_archive import (
    CHAIN_MEMBER_NAMES,
)



# ---------------------------------------------------------------------------
# 状態
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Chain:
    """live chain（state.json が名乗る state と、live にある member）。"""

    chain_id: str
    bootstrap: bool
    prior: Optional[str]
    state: Optional[str]            # state.json が無ければ None
    closed_by: str = "worker"       # RESOLVED にした主体（worker / recovery）
    members: frozenset = frozenset()


@dataclass(frozen=True)
class ModelState:
    deadline: bool = False
    exit: Optional[tuple] = None    # (deadline?, envelope_present, anchor tuple)
    envelope: Optional[str] = None  # "valid" / "invalid" / "valid-rc-mismatch"
    pending: Optional[tuple] = None  # (chain_id, prior, bootstrap)
    live: Optional[Chain] = None
    history: frozenset = frozenset()  # {(resolved_token, chain_id)}
    timeout_members: frozenset = frozenset()
    claimed_disposition: Optional[str] = None
    error_members: frozenset = frozenset()
    error_stage: Optional[str] = None
    archive: Optional[tuple] = None  # (chain_id, resolved_token, moved names frozenset)
    canonical_receipt: bool = False
    projection: Optional[str] = None
    tamper: Optional[str] = None     # malformed 集合だけが使う


def resolved_token(chain: Chain) -> str:
    return f"{chain.chain_id}:RESOLVED:{chain.closed_by}"


def state_token(chain: Chain) -> str:
    return f"{chain.chain_id}:{chain.state}:{chain.closed_by}"


def bootstrap_id(prior: Optional[str]) -> str:
    return f"B[{prior}]"


# ---------------------------------------------------------------------------
# worker（child）の公開の列
# ---------------------------------------------------------------------------

Publication = Callable[[ModelState], ModelState]


def _persist_active(chain_id: str, prior: Optional[str], bootstrap: bool) -> list:
    """``persist_active``: pending を書き、``_commit_pending_active_locked`` で commit。"""

    return [lambda s: replace(s, pending=(chain_id, prior, bootstrap))] + _commit(chain_id, prior, bootstrap)


def _commit(chain_id: str, prior: Optional[str], bootstrap: bool) -> list:
    steps: list = []

    def archive_one(name: str) -> Publication:
        def step(s: ModelState) -> ModelState:
            live = s.live
            members = live.members - {name}
            history = s.history
            if name == layout.STATE:
                history = history | {(resolved_token(live), live.chain_id)}
                return replace(s, live=replace(live, members=members, state=None), history=history)
            return replace(s, live=replace(live, members=members))
        return step

    # 前の RESOLVED chain を member ごとに history へ（state.json は最後）。
    for name in CHAIN_MEMBER_NAMES:
        def maybe(s: ModelState, name=name) -> ModelState:
            if prior is None or s.live is None or s.live.chain_id == chain_id:
                return s
            if name not in s.live.members:
                return s
            return archive_one(name)(s)
        steps.append(maybe)

    def members(s: ModelState, add: str) -> ModelState:
        live = s.live
        if live is None or live.chain_id != chain_id:
            live = Chain(chain_id, bootstrap, prior, None)
        return replace(s, live=replace(live, members=live.members | {add}))

    steps.append(lambda s: members(s, layout.PREFIX_STREAM))
    steps.append(lambda s: members(s, layout.CHECKPOINT))
    steps.append(lambda s: replace(
        s, live=replace(s.live, state=CheckpointState.ACTIVE.value, members=s.live.members | {layout.STATE}),
    ))
    steps.append(lambda s: replace(s, pending=None))
    return steps


def _worker_completion() -> list:
    def add(name: str) -> Publication:
        return lambda s: replace(s, live=replace(s.live, members=s.live.members | {name}))
    return [
        add(layout.CONTINUATION_STREAM), add(layout.CONTINUATION), add(layout.READY),
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.COMPLETION_READY.value)),
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.RESOLVED.value)),
    ]


def worker_script(checkpoints: int, envelope: Optional[str]) -> list:
    """child の公開の列（checkpoint を ``checkpoints`` 回、最後に envelope）。"""

    steps: list = []
    prior: Optional[str] = None
    for index in range(1, checkpoints + 1):
        chain_id = f"c{index}"
        steps += _persist_active(chain_id, prior, False)
        steps += _worker_completion()
        prior = f"{chain_id}:RESOLVED:worker"
    if envelope is not None:
        steps.append(lambda s: replace(s, envelope=envelope))
    return steps


# ---------------------------------------------------------------------------
# supervisor の公開の列（production の store / command と同じ順序）
# ---------------------------------------------------------------------------


def observed_anchor(s: ModelState) -> tuple:
    """``record_child_exit`` が lock の中で観測する anchor。"""

    if s.pending is not None:
        return (ANCHOR_PENDING_ACTIVE, s.pending[0])
    if s.live is not None and s.live.state is not None:
        return (ANCHOR_CHAIN, s.live.chain_id, s.live.state, state_token(s.live))
    return (ANCHOR_NONE,)


DISPOSITION = {"deadline": "SIGTERM_AFTER_DEADLINE", "natural": "EXIT_CODE_X"}


def op_record_exit(kind: str) -> list:
    return [lambda s: replace(
        s, exit=(kind == "deadline", s.envelope is not None, observed_anchor(s)),
    )]


def _anchor_chain(s: ModelState) -> Optional[str]:
    anchor = s.exit[2]
    return anchor[1] if anchor[0] in {ANCHOR_CHAIN, ANCHOR_PENDING_ACTIVE} else None


def op_commit_pending(s: ModelState) -> list:
    chain_id, prior, bootstrap = s.pending
    return _commit(chain_id, prior, bootstrap)


def op_bootstrap(s: ModelState) -> list:
    prior = resolved_token(s.live) if s.live is not None else None
    return _persist_active(bootstrap_id(prior), prior, True)


def op_recover_ready(s: ModelState) -> list:
    return [
        lambda s: replace(s, live=replace(s.live, members=s.live.members | {layout.RECOVERY_RESOLUTION})),
        lambda s: s,  # ready.json（identical）
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.RESOLVED.value, closed_by="recovery")),
    ]


def op_close_continuation(s: ModelState) -> list:
    return [
        lambda s: replace(s, live=replace(s.live, members=s.live.members | {layout.RECOVERY_RESOLUTION})),
        lambda s: replace(s, live=replace(s.live, members=s.live.members | {layout.READY})),
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.COMPLETION_READY.value, closed_by="recovery")),
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.RESOLVED.value, closed_by="recovery")),
    ]


def op_claim(s: ModelState) -> list:
    return [
        lambda s: replace(s, timeout_members=s.timeout_members | {layout.CLAIMED},
                          claimed_disposition=DISPOSITION["deadline"]),
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.TIMED_OUT_CLAIMED.value)),
    ]


def op_finalize_timeout(s: ModelState) -> list:
    return [
        *(lambda s, name=name: replace(s, timeout_members=s.timeout_members | {name})
          for name in layout.TIMEOUT_MEMBERS[1:]),
        lambda s: replace(s, live=replace(s.live, state=CheckpointState.TIMED_OUT.value)),
    ]


def op_issue_canonical(s: ModelState) -> list:
    return [lambda s: replace(s, canonical_receipt=True)]


def op_begin_archive(s: ModelState) -> list:
    return [lambda s: replace(s, archive=(s.live.chain_id, resolved_token(s.live), frozenset()))]


def op_advance_archive(s: ModelState) -> list:
    chain_id, token, _ = s.archive
    steps = []
    for name in CHAIN_MEMBER_NAMES:
        def move(s: ModelState, name=name) -> ModelState:
            live = s.live
            if live is None or name not in live.members:
                return s
            members = live.members - {name}
            archive = (chain_id, token, s.archive[2] | {name})
            if name == layout.STATE:
                return replace(
                    s, live=None if not members else replace(live, members=members, state=None),
                    archive=archive, history=s.history | {(token, chain_id)},
                )
            return replace(s, live=replace(live, members=members), archive=archive)
        steps.append(move)
    return steps


def op_finalize_error(stage: str) -> Callable[[ModelState], list]:
    def publications(s: ModelState) -> list:
        return [
            lambda s, name=name: replace(s, error_members=s.error_members | {name}, error_stage=stage)
            for name in layout.ERROR_MEMBERS
        ]
    return publications


OPERATIONS: dict = {
    tr.StepKind.COMMIT_PENDING_ACTIVE: op_commit_pending,
    tr.StepKind.BOOTSTRAP_ACTIVE: op_bootstrap,
    tr.StepKind.RECOVER_READY: op_recover_ready,
    tr.StepKind.CLOSE_CONTINUATION: op_close_continuation,
    tr.StepKind.CLAIM_TIMEOUT: op_claim,
    tr.StepKind.FINALIZE_TIMEOUT: op_finalize_timeout,
    tr.StepKind.ISSUE_CANONICAL_RESOLVED: op_issue_canonical,
    tr.StepKind.BEGIN_ARCHIVE: op_begin_archive,
    tr.StepKind.ADVANCE_ARCHIVE: op_advance_archive,
}


def operation(step: tr.Step) -> Callable[[ModelState], list]:
    if step.kind is tr.StepKind.FINALIZE_ERROR:
        return op_finalize_error(step.error_stage)
    return OPERATIONS[step.kind]


# ---------------------------------------------------------------------------
# model 状態 -> production の snapshot
# ---------------------------------------------------------------------------


def _anchor(value: tuple) -> CheckpointAnchor:
    if value[0] == ANCHOR_NONE:
        return CheckpointAnchor(ANCHOR_NONE)
    if value[0] == ANCHOR_PENDING_ACTIVE:
        return CheckpointAnchor(
            ANCHOR_PENDING_ACTIVE, checkpoint_receipt_digest=value[1],
            transaction_digest=f"tx:{value[1]}",
        )
    return CheckpointAnchor(
        ANCHOR_CHAIN, checkpoint_receipt_digest=value[1], state=value[2],
        state_receipt_digest=value[3],
    )


def snapshot(s: ModelState, mode: tr.ExitMode) -> tr.TerminalSnapshot:
    V, A, I = tr.Presence.VALID, tr.Presence.ABSENT, tr.Presence.INVALID
    tamper = s.tamper or ""
    deadline = tr.Fact(V, "D") if s.deadline else tr.Fact()
    if tamper == "D":
        deadline = tr.Fact(I, detail="signature mismatch")
    exit_fact = tr.ExitFact()
    if s.exit is not None:
        is_deadline, envelope_present, anchor = s.exit
        exit_fact = tr.ExitFact(
            V, "E", returncode=(-15 if is_deadline else 2),
            disposition=DISPOSITION["deadline" if is_deadline else "natural"],
            deadline_digest="D" if is_deadline else None,
            envelope_sha256="env" if envelope_present else None,
            anchor=_anchor(anchor),
        )
        if tamper == "E":
            exit_fact = tr.ExitFact(I, detail="signature mismatch")
    pending = tr.PendingFact()
    if s.pending is not None:
        chain_id, prior, bootstrap = s.pending
        pending = tr.PendingFact(
            V, f"tx:{chain_id}", checkpoint_digest=chain_id,
            prior_resolved_digest=prior, is_bootstrap=bootstrap,
        )
        if tamper == "pending":
            pending = tr.PendingFact(I, detail="transaction digest drifted")
    archive = tr.ArchiveFact()
    live = tr.LiveChainFact()
    if s.archive is not None:
        chain_id, token, moved = s.archive
        remaining = s.live is not None and bool(s.live.members)
        archive = tr.ArchiveFact(
            V, "A", checkpoint_digest=chain_id, resolved_digest=token,
            stage=ErrorStage.NON_DECOMPILATION.value,
            union=tr.UnionState.PARTIAL if remaining else tr.UnionState.COMPLETE,
        )
        if tamper == "A":
            archive = tr.ArchiveFact(I, detail="manifest signature mismatch")
        if tamper == "foreign-live":
            archive = replace(archive, union=tr.UnionState.CONFLICT, detail="live chain outside the manifest")
        live = tr.LiveChainFact(tr.LiveKind.ARCHIVING if remaining else tr.LiveKind.NONE)
    elif s.pending is not None:
        predecessor = s.live if s.live is not None and s.live.state is not None else None
        live = tr.LiveChainFact(
            tr.LiveKind.IN_TRANSACTION,
            checkpoint_digest=None if predecessor is None else predecessor.chain_id,
            is_bootstrap=False if predecessor is None else predecessor.bootstrap,
            state=None if predecessor is None else predecessor.state,
            state_digest=None if predecessor is None else state_token(predecessor),
        )
    elif s.live is not None:
        chain = s.live
        if chain.state is None:
            live = tr.LiveChainFact(tr.LiveKind.INVALID, detail="chain members without state")
        else:
            has_cont = {layout.CONTINUATION, layout.CONTINUATION_STREAM} <= chain.members
            live = tr.LiveChainFact(
                tr.LiveKind.CHAIN, checkpoint_digest=chain.chain_id,
                is_bootstrap=chain.bootstrap, prior_resolved_digest=chain.prior,
                state=chain.state, state_digest=state_token(chain),
                continuation=V if has_cont else A,
                kill_disposition=(
                    s.claimed_disposition
                    if chain.state in {CheckpointState.TIMED_OUT_CLAIMED.value, CheckpointState.TIMED_OUT.value} else None
                ),
            )
    if tamper == "live":
        live = tr.LiveChainFact(tr.LiveKind.INVALID, detail="state signature mismatch")
    if tamper == "foreign-live" and s.archive is None:
        live = tr.LiveChainFact(
            tr.LiveKind.CHAIN, checkpoint_digest="foreign", state=CheckpointState.ACTIVE.value,
            state_digest="foreign:ACTIVE", continuation=A,
        )
        pending = tr.PendingFact()
    timeout_complete = (
        s.live is not None and s.live.state == CheckpointState.TIMED_OUT.value
        and set(layout.TIMEOUT_MEMBERS) <= s.timeout_members
    )
    timeout = tr.TimeoutFact(
        members=frozenset(s.timeout_members), complete=timeout_complete,
        bundle_digest="T" if timeout_complete else None,
    )
    error_complete = set(layout.ERROR_MEMBERS) <= s.error_members
    error = tr.ErrorFact(
        members=frozenset(s.error_members), complete=error_complete,
        stage=s.error_stage,
        disposition=(exit_fact.disposition if s.error_members else None),
        bundle_digest="X" if error_complete else None,
    )
    envelope_presence = {
        None: A, "valid": V, "invalid": I, "valid-rc-mismatch": V,
    }[s.envelope]
    canonical = tr.CanonicalFact(
        receipt=V if s.canonical_receipt else A,
        envelope=envelope_presence,
        envelope_sha256="env" if s.envelope is not None else None,
        envelope_cli_returncode=(
            2 if s.envelope == "valid" else 3 if s.envelope == "valid-rc-mismatch" else None
        ),
        detail="seal mismatch" if s.envelope == "invalid" else None,
    )
    history = {token: chain_id for token, chain_id in s.history}
    return tr.TerminalSnapshot(
        mode=mode, launch=tr.Fact(V, "L"), deadline=deadline, child_exit=exit_fact,
        child_alive=False if s.exit is not None else None,
        pending=pending, live=live, timeout=timeout, error=error,
        archive=archive, canonical=canonical, history=history,
    )


# ---------------------------------------------------------------------------
# scenario と oracle
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Scenario:
    checkpoints: int
    child_steps: int        # child が終わるまでに公開した数
    termination: str        # "deadline" / "natural"
    mode: tr.ExitMode
    envelope: Optional[str]
    exit_durable: bool      # supervisor が E を durable にしたか
    worker: tuple = field(default=(), compare=False, repr=False)


def worker_phase(state: ModelState) -> str:
    """child が終わった時点の checkpoint の段階（oracle の入力。next_step は見ない）。"""

    if state.pending is not None:
        return "PENDING"
    if state.live is None or state.live.state is None:
        return "NONE"
    if state.live.state == CheckpointState.ACTIVE.value:
        members = state.live.members
        return "ACTIVE_CONT" if {layout.CONTINUATION, layout.CONTINUATION_STREAM} <= members else "ACTIVE"
    return state.live.state


def expected_terminal(scenario: Scenario, phase: str) -> tuple:
    """仕様（計画 v5 §6.3 / §6.5 とユーザー判断の mode 分け）から終端を決める。"""

    if not scenario.exit_durable:
        return ("INVALID", "DEADLINE_WITHOUT_EXIT_OBSERVATION"
                if scenario.termination == "deadline" else "EXIT_NOT_OBSERVED")
    if scenario.termination == "deadline":
        return ("TIMEOUT", None)
    if scenario.mode is tr.ExitMode.CANONICAL_RESULT_REQUIRED:
        return ("RESOLVED", None) if scenario.envelope == "valid" else (
            "INVALID", "CANONICAL_CHILD_RESULT_INVALID")
    if phase == "NONE":
        return ("ERROR", ErrorStage.BEFORE_CHECKPOINT.value)
    if phase in {"ACTIVE", "PENDING"}:
        return ("INVALID", "ACTIVE_EXIT_STAGE_UNSEALED")
    return ("ERROR", ErrorStage.NON_DECOMPILATION.value)


def terminal_of(step: tr.Step, state: ModelState) -> tuple:
    if step.kind is tr.StepKind.INVALID:
        return ("INVALID", step.invalid_code.value)
    if step.kind is tr.StepKind.ADOPT_ERROR:
        return ("ERROR", state.error_stage)
    return ({
        tr.StepKind.ADOPT_TIMEOUT: "TIMEOUT", tr.StepKind.ADOPT_RESOLVED: "RESOLVED",
    }[step.kind], None)


# ---------------------------------------------------------------------------
# 探索
# ---------------------------------------------------------------------------


class ModelFailure(AssertionError):
    pass


def drive(state: ModelState, mode: tr.ExitMode, *, crash_after: Optional[int] = None,
          limit: int = 64) -> tuple[ModelState, Optional[tr.Step], list]:
    """crash 無しなら終端まで、``crash_after`` なら通算その公開数の直後で止める。

    返り値: (最後の状態, 終端の step（crash したら None）, 通った状態の列)。
    """

    seen = [state]
    published = 0
    for _ in range(limit):
        try:
            step = tr.next_step(snapshot(state, mode))
        except Exception as exc:  # noqa: BLE001 - model は unhandled を数える
            raise ModelFailure(f"next_step raised {type(exc).__name__}: {exc} at {state}") from exc
        if step.terminal:
            if step.kind is tr.StepKind.INVALID and not (step.invalid_code and step.detail):
                raise ModelFailure(f"INVALID without code/detail at {state}")
            publications = [lambda s: replace(s, projection=step.kind.value)]
            for publication in publications:
                if crash_after is not None and published == crash_after:
                    return state, None, seen
                state = publication(state)
                published += 1
            return state, step, seen
        before = state
        for publication in operation(step)(state):
            if crash_after is not None and published == crash_after:
                return state, None, seen
            state = publication(state)
            published += 1
        if state == before:
            raise ModelFailure(f"{step.kind.value} did not change the durable state at {before}")
        if state in seen:
            raise ModelFailure(f"cycle through {step.kind.value} at {state}")
        seen.append(state)
    raise ModelFailure(f"drive did not terminate from {seen[0]}")


def scenarios() -> Iterable[tuple[Scenario, ModelState]]:
    for checkpoints in (0, 1, 2):
        for envelope in (None, "valid", "invalid", "valid-rc-mismatch"):
            script = worker_script(checkpoints, envelope)
            state = ModelState()
            prefixes = [state]
            for publication in script:
                state = publication(state)
                prefixes.append(state)
            for steps, child_state in enumerate(prefixes):
                for termination in ("deadline", "natural"):
                    for mode in tr.ExitMode:
                        for exit_durable in (True, False):
                            scenario = Scenario(
                                checkpoints, steps, termination, mode,
                                child_state.envelope, exit_durable,
                            )
                            start = child_state
                            if termination == "deadline":
                                start = replace(start, deadline=True)
                            if exit_durable:
                                start = op_record_exit(termination)[0](start)
                            yield scenario, start


def explore() -> dict:
    reachable: dict = {}
    transitions = 0
    for scenario, start in scenarios():
        phase = worker_phase(replace(start, deadline=False, exit=None))
        oracle = expected_terminal(scenario, phase)
        frontier = [start]
        while frontier:
            state = frontier.pop()
            key = (state, scenario.mode)
            if key in reachable:
                previous = reachable[key]
                if previous != oracle:
                    raise ModelFailure(
                        f"one reachable state has two oracles {previous} / {oracle}: {state}"
                    )
                continue
            reachable[key] = oracle
            final, step, _ = drive(state, scenario.mode)
            if final != state:
                # 終端の公開（projection）の直後に落ちた状態も reachable。
                frontier.append(final)
            got = terminal_of(step, final)
            if got != oracle:
                raise ModelFailure(
                    f"{scenario} phase={phase}: expected {oracle}, drive reached {got} from {state}"
                )
            crash_points = 0
            while True:
                crashed, step, _ = drive(state, scenario.mode, crash_after=crash_points)
                if step is not None:
                    break
                transitions += 1
                frontier.append(crashed)
                crash_points += 1
    return {"reachable": reachable, "transitions": transitions}


# ---------------------------------------------------------------------------
# malformed / tampered（別集合）
# ---------------------------------------------------------------------------

TAMPERS = {
    "D": lambda s: s.deadline,
    "E": lambda s: s.exit is not None,
    "A": lambda s: s.archive is not None,
    "pending": lambda s: s.pending is not None,
    "live": lambda s: s.live is not None and s.archive is None and s.pending is None,
    "foreign-live": lambda s: s.exit is not None and s.exit[0] is False and (
        s.archive is not None or s.live is None or s.live.state == CheckpointState.RESOLVED.value),
}

CONFLICTS = {
    # 完成した ERROR に TIMEOUT の物件を足す / その逆 / RESOLVED に D を足す。
    "timeout-on-error": (
        lambda s: bool(s.error_members),
        lambda s: replace(s, timeout_members=s.timeout_members | {layout.CLAIMED}),
    ),
    "error-on-timeout": (
        lambda s: bool(s.timeout_members),
        lambda s: replace(s, error_members=s.error_members | {layout.OPERATIONAL_ERROR},
                          error_stage=ErrorStage.BEFORE_CHECKPOINT.value),
    ),
    "deadline-on-resolved": (
        lambda s: s.canonical_receipt,
        lambda s: replace(s, deadline=True),
    ),
    "resolved-on-timeout": (
        lambda s: bool(s.timeout_members),
        lambda s: replace(s, canonical_receipt=True),
    ),
    "claim-disposition-mismatch": (
        lambda s: s.claimed_disposition is not None and s.live is not None
        and s.live.state in {CheckpointState.TIMED_OUT_CLAIMED.value, CheckpointState.TIMED_OUT.value},
        lambda s: replace(s, claimed_disposition="SIGKILL_AFTER_DEADLINE"),
    ),
}


def check_malformed(reachable: dict) -> dict:
    counts = {name: 0 for name in (*TAMPERS, *CONFLICTS, "unrelated-history")}
    for (state, mode), oracle in reachable.items():
        for name, applies in TAMPERS.items():
            if not applies(state):
                continue
            step = tr.next_step(snapshot(replace(state, tamper=name), mode))
            if step.kind is not tr.StepKind.INVALID:
                raise ModelFailure(f"tamper {name} was not rejected first: {step} at {state}")
            counts[name] += 1
        for name, (applies, mutate) in CONFLICTS.items():
            if not applies(state):
                continue
            step = tr.next_step(snapshot(mutate(state), mode))
            if step.kind is not tr.StepKind.INVALID:
                raise ModelFailure(f"conflict {name} was not rejected first: {step} at {state}")
            counts[name] += 1
        # 対照: 無関係な古い history は終端を変えない。
        control = replace(state, history=state.history | {("old:RESOLVED:worker", "old")})
        final, step, _ = drive(control, mode)
        if terminal_of(step, final) != oracle:
            raise ModelFailure(f"unrelated history changed the terminal at {state}")
        counts["unrelated-history"] += 1
    return counts


def main() -> int:
    result = explore()
    reachable = result["reachable"]
    terminals: dict = {}
    for oracle in reachable.values():
        terminals[f"{oracle[0]}:{oracle[1]}"] = terminals.get(f"{oracle[0]}:{oracle[1]}", 0) + 1
    malformed = check_malformed(reachable)
    print(json.dumps({
        "reachable_states": len(reachable),
        "crash_transitions": result["transitions"],
        "terminal_oracles": dict(sorted(terminals.items())),
        "malformed_rejected": malformed,
        "cycles": 0, "unhandled": 0,
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
