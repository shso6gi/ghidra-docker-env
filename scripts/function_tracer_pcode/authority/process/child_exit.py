"""worker child の終了観測の語彙（rc の取り方・disposition・送った signal）。

この module が語彙と対応規則の唯一の owner（Issue #165）。

* supervisor（``supervisor_command``）が作る disposition と、E（``child-exit.json``）
  に残す signal の結果。
* 分類器・pair-status の封（``canonical_result`` / ``pair_status_authority``）と
  reporting が行う「rc と disposition の join」。

どれも同じ関数で判定し、別 module に条件を写さない。この module は標準
library しか import しない（process の起動・store・分類器に依存しない）。

disposition の形:

``EXIT_CODE_<rc>``
    signal を送っていない自然終了。
``SIGTERM_AFTER_DEADLINE`` / ``SIGKILL_AFTER_DEADLINE``
    deadline 後に送った signal で終わった。
``EXITED_<rc>[_BEFORE_SIGTERM|_AFTER_SIGTERM|_BEFORE_SIGKILL|_AFTER_SIGKILL]``
    deadline 後の終了処理の途中で、signal 以外の理由で終わった。
"""

from __future__ import annotations

from enum import Enum
import re

#: rc の取り方。``LIVE_PROCESS_WAIT`` は wait / poll の返り値そのもの。
LIVE_PROCESS_WAIT = "LIVE_PROCESS_WAIT"
#: #165 より前の restart が書いた、rc の無い観測（既存の pair-status と log を
#: 読むために語彙に残す。#165 の後の supervisor は作らない: restart も E の rc を使い、
#: E が無ければ終端にせず INVALID にする）。
DURABLE_RESTART_NO_CHILD_STATUS = "DURABLE_RESTART_NO_CHILD_STATUS"
OBSERVATION_KINDS = frozenset({LIVE_PROCESS_WAIT, DURABLE_RESTART_NO_CHILD_STATUS})

SIGTERM = "SIGTERM"
SIGKILL = "SIGKILL"
SIGNAL_NAMES = frozenset({SIGTERM, SIGKILL})
#: ``killpg`` を呼んで戻った（``sent``）か、対象が既に居なかった（``process_absent``）か。
SIGNAL_SENT = "sent"
SIGNAL_PROCESS_ABSENT = "process_absent"
SIGNAL_RESULTS = frozenset({SIGNAL_SENT, SIGNAL_PROCESS_ABSENT})


class DeadlinePhase(str, Enum):
    """deadline 後の終了処理（SIGTERM -> grace -> SIGKILL）のどこで child が終わったか。"""

    BEFORE_SIGTERM = "BEFORE_SIGTERM"
    AFTER_SIGTERM = "AFTER_SIGTERM"
    BEFORE_SIGKILL = "BEFORE_SIGKILL"
    AFTER_SIGKILL = "AFTER_SIGKILL"


SIGTERM_AFTER_DEADLINE = "SIGTERM_AFTER_DEADLINE"
SIGKILL_AFTER_DEADLINE = "SIGKILL_AFTER_DEADLINE"
#: signal そのもので終わったときの disposition と、そのときの rc（Linux の値）。
_SIGNAL_RETURNCODES = {SIGTERM_AFTER_DEADLINE: -15, SIGKILL_AFTER_DEADLINE: -9}
#: 送った直後の phase -> その signal で終わったときの disposition。
_SIGNAL_DEATH = {
    DeadlinePhase.AFTER_SIGTERM: SIGTERM_AFTER_DEADLINE,
    DeadlinePhase.AFTER_SIGKILL: SIGKILL_AFTER_DEADLINE,
}
_CODE = r"-?[0-9]+"
_NATURAL = re.compile(rf"\AEXIT_CODE_({_CODE})\Z")
_DEADLINE_EXIT = re.compile(
    rf"\AEXITED_({_CODE})(?:_({'|'.join(phase.value for phase in DeadlinePhase)}))?\Z"
)

_TERM_SENT = (SIGTERM, SIGNAL_SENT)
#: deadline 後の disposition -> それを返しうる ``killpg`` の結果の列
#: （終了処理の枝ごと）。key の None は「signal を送る前に終わっていた」。
_DEADLINE_SIGNAL_ACTIONS = {
    SIGTERM_AFTER_DEADLINE: frozenset({(_TERM_SENT,)}),
    SIGKILL_AFTER_DEADLINE: frozenset({(_TERM_SENT, (SIGKILL, SIGNAL_SENT))}),
    None: frozenset({()}),
    DeadlinePhase.BEFORE_SIGTERM.value: frozenset({((SIGTERM, SIGNAL_PROCESS_ABSENT),)}),
    DeadlinePhase.AFTER_SIGTERM.value: frozenset({(_TERM_SENT,)}),
    DeadlinePhase.BEFORE_SIGKILL.value: frozenset({
        (_TERM_SENT,), (_TERM_SENT, (SIGKILL, SIGNAL_PROCESS_ABSENT)),
    }),
    DeadlinePhase.AFTER_SIGKILL.value: frozenset({(_TERM_SENT, (SIGKILL, SIGNAL_SENT))}),
}


def deadline_exit_disposition(returncode: int, phase: "DeadlinePhase | None") -> str:
    """deadline 後の終了処理で観測した rc の disposition（supervisor が作る唯一の入口）。

    送った signal の直後に、その signal の rc で終わったなら ``*_AFTER_DEADLINE``。
    それ以外は ``EXITED_<rc>[_<phase>]``（phase が None なら signal を送る前）。
    """

    if type(returncode) is not int:
        raise ValueError("child return code must be an exact int")
    signal_death = _SIGNAL_DEATH.get(phase)
    if signal_death is not None and returncode == _SIGNAL_RETURNCODES[signal_death]:
        return signal_death
    suffix = "" if phase is None else f"_{phase.value}"
    return f"EXITED_{returncode}{suffix}"


def natural_exit_disposition(returncode: int) -> str:
    """signal を送っていない終了の disposition。"""

    if type(returncode) is not int:
        raise ValueError("child return code must be an exact int")
    return f"EXIT_CODE_{returncode}"


def disposition_returncode(disposition: str) -> int:
    """disposition が名指す rc（封の語彙に無い disposition は ValueError）。"""

    if type(disposition) is not str or not disposition:
        raise ValueError("durable child exit disposition is missing")
    if disposition in _SIGNAL_RETURNCODES:
        return _SIGNAL_RETURNCODES[disposition]
    match = _NATURAL.match(disposition) or _DEADLINE_EXIT.match(disposition)
    if match is None:
        if disposition.startswith(("EXIT_CODE_", "EXITED_")):
            raise ValueError("child exit disposition code is malformed")
        raise ValueError(
            "live return code is not derivable from durable disposition authority"
        )
    return int(match.group(1))


def deadline_signal_actions(disposition: str) -> frozenset:
    """deadline 後の終了処理で、その disposition を返しうる signal 送信の列。

    deadline の disposition でなければ空集合（自然終了の ``EXIT_CODE_`` も空）。
    disposition と実際に送った signal を別々に記録するので、両者が同じ終了処理
    の 1 つの枝として説明できることをこの対応で確かめる。
    """

    if type(disposition) is not str:
        return frozenset()
    if disposition in _SIGNAL_RETURNCODES:
        return _DEADLINE_SIGNAL_ACTIONS[disposition]
    match = _DEADLINE_EXIT.match(disposition)
    if match is None:
        return frozenset()
    return _DEADLINE_SIGNAL_ACTIONS[match.group(2)]


def is_deadline_disposition(disposition: object) -> bool:
    """supervisor の deadline 経路が作り得る disposition か（完全一致）。"""

    return bool(deadline_signal_actions(disposition))  # type: ignore[arg-type]


def validate_durable_child_returncode_observation(
    *, child_exit_disposition: str, child_returncode: object,
    observation_kind: str,
) -> None:
    """OS の rc を、署名された disposition と観測の種類に join する。

    ``DURABLE_RESTART_NO_CHILD_STATUS``（#165 より前の記録）は rc を持たない。
    live の観測は exact int の rc が disposition の名指す rc と一致しなければ
    ならない。
    """

    if type(child_exit_disposition) is not str or not child_exit_disposition:
        raise ValueError("durable child exit disposition is missing")
    if observation_kind == DURABLE_RESTART_NO_CHILD_STATUS:
        if child_returncode is not None:
            raise ValueError("durable restart cannot invent a child return code")
        return
    if observation_kind != LIVE_PROCESS_WAIT:
        raise ValueError("child return-code observation kind is invalid")
    if type(child_returncode) is not int:
        raise ValueError("live terminal observation lacks an exact return code")
    if child_returncode != disposition_returncode(child_exit_disposition):
        raise ValueError("child return code differs from durable disposition")
