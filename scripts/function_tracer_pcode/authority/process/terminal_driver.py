"""Issue #165: 終端までの loop（run と restart で共通）。

``drive`` は ``run()`` が D / E を durable にした後と、``_resume()`` の両方から
呼ばれる唯一の終端処理。1 周ごとに store の flock を 1 回取り、その中で

snapshot の再読 → ``next_step`` → 1 つの durable 操作（または終端の採用）

を行う。前の周の観測を次の周の書込みに使わない（stale snapshot で書かない）。

進捗の保証: progress 操作のあと store の durable な file 集合（fingerprint）が
変わらなければ、また既に通った集合へ戻れば、その場で INVALID にする
（``NO_PROGRESS``。無制限の busy loop にしない）。周回の上限も持つ。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Optional

from scripts.function_tracer_pcode.authority.process import terminal_recovery as recovery
from scripts.function_tracer_pcode.authority.process.terminal_snapshot import (
    store_fingerprint,
)
from scripts.function_tracer_pcode.authority.process.terminal_transaction import (
    TerminalAuthority,
    open_transaction,
)

#: 1 つの store で起こりうる progress 操作の数は有限（chain 1 つの close / claim /
#: finalize、archive の member、bootstrap の commit …）。これを超えたら進んでいない。
MAX_STEPS = 64


@dataclass(frozen=True)
class DriveResult:
    """``drive`` の結果: 採用した終端か、INVALID の code と detail。"""

    authority: Optional[TerminalAuthority]
    invalid_code: Optional[str] = None
    detail: Optional[str] = None
    #: INVALID の診断（child の PID / start token と生存観測など）。
    diagnostics: Optional[dict] = None
    #: E が durable なら、その実測 rc（INVALID の projection にも載せる）。
    child_returncode: Optional[int] = None
    steps: tuple = ()


def drive(
    store: Any, ownership: Any, *, mode: recovery.ExitMode,
    process_alive: Callable[[int, str], Optional[bool]],
) -> DriveResult:
    seen: set[str] = set()
    taken: list[str] = []
    for _ in range(MAX_STEPS):
        with open_transaction(store, ownership) as transaction:
            snapshot, context = transaction.snapshot(mode=mode, process_alive=process_alive)
            step = recovery.next_step(snapshot)
            returncode = snapshot.child_exit.returncode
            if step.kind is recovery.StepKind.INVALID:
                return DriveResult(
                    None, step.invalid_code.value, step.detail,
                    diagnostics=_diagnostics(snapshot, context),
                    child_returncode=returncode, steps=tuple(taken),
                )
            if step.terminal:
                return DriveResult(
                    transaction.adopt(step, context),
                    child_returncode=returncode, steps=tuple(taken + [step.kind.value]),
                )
            before = context.fingerprint
            if before in seen:
                return _no_progress(step, snapshot, "returned to an earlier durable state", taken)
            seen.add(before)
            transaction.execute(step, context)
            taken.append(step.kind.value)
            if store_fingerprint(store.directory) == before:
                return _no_progress(step, snapshot, "did not change the durable state", taken)
    return DriveResult(
        None, recovery.InvalidCode.NO_PROGRESS.value,
        f"no terminal after {MAX_STEPS} operations", steps=tuple(taken),
    )


@dataclass(frozen=True)
class Inspection:
    """読むだけの判断（分類器用）: 次の 1 手と、終端なら採用した authority。"""

    step: recovery.Step
    snapshot: recovery.TerminalSnapshot
    authority: Optional[TerminalAuthority]


def inspect(
    store: Any, *, mode: Optional[recovery.ExitMode],
    process_alive: Callable[[int, str], Optional[bool]],
) -> Inspection:
    """durable authority を書かずに、supervisor と同じ判断で終端を読む。

    supervisor と同じ owner lock と store の flock を取る（終端処理の途中の
    store を読まない。lock file が無ければ作るが、authority の file は書かない）。``mode`` が None なら E に記録された mode で読む。
    採用する終端（ADOPT_*）なら ``drive`` と同じ ``adopt`` で authority を作る。
    """

    with store.supervisor_ownership() as ownership:
        with open_transaction(store, ownership) as transaction:
            snapshot, context = transaction.snapshot(mode=mode, process_alive=process_alive)
            step = recovery.next_step(snapshot)
            authority = (
                transaction.adopt(step, context)
                if step.terminal and step.kind is not recovery.StepKind.INVALID
                else None
            )
            return Inspection(step, snapshot, authority)


def _no_progress(
    step: recovery.Step, snapshot: recovery.TerminalSnapshot, why: str, taken: list,
) -> DriveResult:
    return DriveResult(
        None, recovery.InvalidCode.NO_PROGRESS.value, f"{step.kind.value} {why}",
        child_returncode=snapshot.child_exit.returncode, steps=tuple(taken),
    )


def _diagnostics(snapshot: recovery.TerminalSnapshot, context: Any) -> dict:
    """INVALID の理由を追うための観測（判定には使わない）。

    D だけで restart した場合（計画 v5 §6.3）: child の PID / start token と
    いま生きているかを残す。停止は既存の cleanup 手順へ渡す（ここでは kill
    しない・signal 死を推定しない）。
    """

    launch = context.launch
    if launch is None:
        return {}
    return {
        "child_pid": launch.payload["child_pid"],
        "child_start_token": launch.payload["child_start_token"],
        "child_alive_at_decision": snapshot.child_alive,
        "deadline_receipt": snapshot.deadline.presence.value,
        "child_exit_receipt": snapshot.child_exit.presence.value,
    }
