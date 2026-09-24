"""durable checkpoint の state、共有する receipt kind、supervisor が封をする ERROR の種類・stage の語彙。

語彙の owner はこの module だけ（Issue #165）。store（``supervisor``）・
snapshot・復旧判断（``terminal_recovery``）・test はここから import する。
値を別の module へ文字列で写して drift test で揃える、ということはしない。

この module は何も import しない（store や判断の module に依存しない）ので、
純関数の復旧判断からも store からも同じ語彙を使える。
"""

from __future__ import annotations

from enum import Enum


class CheckpointState(str, Enum):
    """``CheckpointStateTransitionReceipt`` の ``state``。"""

    ACTIVE = "ACTIVE"
    COMPLETION_READY = "COMPLETION_READY"
    RESOLVED = "RESOLVED"
    TIMED_OUT_CLAIMED = "TIMED_OUT_CLAIMED"
    TIMED_OUT = "TIMED_OUT"


#: 許される state の遷移（store の transition issuer が検査する）。
ALLOWED_TRANSITIONS = frozenset({
    (CheckpointState.ACTIVE, CheckpointState.COMPLETION_READY),
    (CheckpointState.COMPLETION_READY, CheckpointState.RESOLVED),
    (CheckpointState.ACTIVE, CheckpointState.TIMED_OUT_CLAIMED),
    (CheckpointState.TIMED_OUT_CLAIMED, CheckpointState.TIMED_OUT),
})

#: timeout の chain にある state（claim した後）。
TIMEOUT_STATES = frozenset({CheckpointState.TIMED_OUT_CLAIMED, CheckpointState.TIMED_OUT})


#: store と終端の module が共有する receipt の kind（署名・schema は ``supervisor``）。
LAUNCH_RECEIPT_KIND = "SupervisorLaunchReceipt"
#: deadline の後に supervisor が作る ACTIVE checkpoint（worker の prefix が無いとき）。
BOOTSTRAP_CHECKPOINT_KIND = "SupervisorBootstrapCheckpointReceipt"


#: supervisor が自分で終端として封をする ERROR の種類（child の終了を
#: operational ERROR にするときの ``error_kind``）。
SUPERVISOR_EXIT_ERROR_KIND = "operational_authority_invalid"
SUPERVISOR_OPERATIONAL_ERROR_KINDS = frozenset({SUPERVISOR_EXIT_ERROR_KIND})


class ErrorStage(str, Enum):
    """supervisor の operational ERROR が封をする ``deadline_stage``。

    ``DURING_DECOMPILATION`` は無い（Issue #165 Phase 0 gate G3）。decompile の
    途中で終わった child は ERROR にせず INVALID にする。stage を足すときは
    ここに 1 行足す（issuer の検査と復旧判断は両方この enum を読む）。
    """

    BEFORE_CHECKPOINT = "BEFORE_CHECKPOINT"
    NON_DECOMPILATION = "NON_DECOMPILATION"


SUPERVISOR_DEADLINE_STAGES = frozenset(stage.value for stage in ErrorStage)
