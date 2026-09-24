"""durable checkpoint store（``<root>/<execution nonce>/``）の file 名の唯一の owner。

store（``supervisor``）・archive（``checkpoint_archive``）・終端の snapshot・
supervisor の CLI・分類器は、store の file をここの名前でだけ名指す。file を
足す・名前を変えるときに触るのはこの module と、その file の中身（schema）を
持つ module だけ。

中身の schema の owner は別:

* checkpoint chain / timeout / operational error の receipt: ``supervisor``
* D / E / A（``deadline.json`` など）: ``terminal_evidence``（kind と file の対応も）
* canonical 結果の envelope と resolved receipt: ``canonical_envelope``

この module は何も import しない。
"""

from __future__ import annotations

LAUNCH = "launch.json"

# -- checkpoint chain（worker の ACTIVE → READY → RESOLVED） -------------------
PENDING_ACTIVE_TRANSACTION = "pending-active-transaction.json"
PREFIX_STREAM = "checkpoint-prefix-stream.json"
CHECKPOINT = "checkpoint.json"
CONTINUATION_STREAM = "continuation-stream.json"
CONTINUATION = "continuation.json"
READY = "ready.json"
RECOVERY_RESOLUTION = "recovery-resolution.json"
STATE = "state.json"

# -- supervisor の TIMEOUT（claim → finalize） ----------------------------------
CLAIMED = "claimed.json"
TIMEOUT = "timeout.json"
TERMINAL_SEGMENT = "terminal-segment.json"
TERMINAL_STREAM = "terminal-stream.json"
#: TIMEOUT の bundle を構成する file（claim が最初）。
TIMEOUT_MEMBERS = (CLAIMED, TIMEOUT, TERMINAL_SEGMENT, TERMINAL_STREAM)

# -- supervisor の operational ERROR --------------------------------------------
OPERATIONAL_ERROR = "operational-error.json"
OPERATIONAL_ERROR_SEGMENT = "operational-error-segment.json"
OPERATIONAL_ERROR_STREAM = "operational-error-stream.json"
OPERATIONAL_ERROR_BUNDLE = "operational-error-bundle.json"
#: ERROR の bundle を構成する file（error receipt が最初）。
ERROR_MEMBERS = (
    OPERATIONAL_ERROR, OPERATIONAL_ERROR_SEGMENT, OPERATIONAL_ERROR_STREAM,
    OPERATIONAL_ERROR_BUNDLE,
)

#: worker / supervisor の checkpoint authority（archive / rollback / 掃除の対象）。
CHECKPOINT_AUTHORITY_FILENAMES = (
    PENDING_ACTIVE_TRANSACTION, CHECKPOINT, STATE, PREFIX_STREAM, CONTINUATION,
    CONTINUATION_STREAM, READY, RECOVERY_RESOLUTION, *TIMEOUT_MEMBERS,
)
