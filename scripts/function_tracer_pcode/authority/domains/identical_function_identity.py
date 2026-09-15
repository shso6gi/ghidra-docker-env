# -*- coding: utf-8 -*-
"""同一バイナリ・同一関数の identity proof（Issue #15）。

比較対象の 2 つの入力が「同じ内容のバイナリ」で「同じ名前の関数がそれぞれ
ちょうど 1 つ」あり、その entry / body / image base / language / compiler spec が
すべて一致するなら、両者の観測可能な意味は同一である。この module はその観測を
**session に束縛した proof artifact** として封じ、既存の decisive proof kind
`EQ_CLOSURE` の event を 1 回だけ発行する encoder を提供する。

新しい proof kind も新しい event type も作らない。EQUIVALENT の門は
`authority.decision.decision.finalize_decision`（`EQ_CLOSURE` の decisive receipt
と `c_active_base` の非阻害）1 つだけで、この経路もそこを通る。

この module は Ghidra object を触らない（`ghidra/` を import しない）。identity は
呼び出し側が観測した値として渡され、ここでは型と一致だけを検証する。cause を
出さないので reason registry / recovery registry は持たない。producer site ID は
呼び出し側の emitter 引数が持つ（ここには定数を置かない）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Tuple

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    DecisiveProofEventAuthority,
    EventIntent,
    EventType,
)


IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA = "identical_function_identity_proof_v1"
IDENTICAL_FUNCTION_IDENTITY_PRODUCER_ID = "identical-function-identity-producer-v1"

#: 二重発行を拒否するための session 側の台帳 key。
IDENTICAL_FUNCTION_IDENTITY_COMMITTED_KEY = "identical_function_identity_committed"

_SIGNAL_TOKEN = object()
_SHA256_HEX_DIGITS = frozenset("0123456789abcdef")

#: artifact body のうち、左右の Program から観測した identity 側の field。
_IDENTITY_FIELDS = (
    "executable_sha256", "language_id", "compiler_spec_id", "image_base",
    "entry", "body_range", "match_count",
)

#: artifact body のうち、この実行（session）へ束縛する field。
_BINDING_FIELDS = (
    "result_occurrence_id", "execution_identity_digest",
    "left_binary_id", "right_binary_id", "binary_content_identity",
    "function_name", "observation_contract_id",
)


def _exact_text(value: Any, what: str) -> str:
    if type(value) is not str or not value:
        raise ValueError(f"identical function identity {what} is not an exact string")
    return value


def _exact_int(value: Any, what: str) -> int:
    if type(value) is not int or type(value) is bool:
        raise ValueError(f"identical function identity {what} is not an exact int")
    return value


def _exact_address(value: Any, what: str) -> Tuple[str, int]:
    pair = tuple(value) if type(value) in (tuple, list) else None
    if pair is None or len(pair) != 2:
        raise ValueError(f"identical function identity {what} is not an address pair")
    return (_exact_text(pair[0], f"{what} space"), _exact_int(pair[1], f"{what} offset"))


def _content_identity_sha256(value: Any) -> str:
    """`sha256:<hex>` の operational 表現から hex を取り出す。"""

    text = _exact_text(value, "binary content identity")
    prefix, separator, digest = text.partition(":")
    if (
        prefix != "sha256"
        or not separator
        or len(digest) != 64
        or not set(digest) <= _SHA256_HEX_DIGITS
    ):
        raise ValueError("identical function identity content identity is not canonical")
    return digest


@dataclass(frozen=True)
class IdenticalFunctionIdentitySessionBinding:
    """artifact を 1 回の実行・1 つの pair・1 つの関数へ束縛する事実。"""

    result_occurrence_id: str
    execution_identity_digest: str
    left_binary_id: str
    right_binary_id: str
    binary_content_identity: str
    function_name: str
    observation_contract_id: str

    def __post_init__(self) -> None:
        for name in _BINDING_FIELDS:
            _exact_text(getattr(self, name), name)
        _content_identity_sha256(self.binary_content_identity)

    def as_body_fields(self) -> Mapping[str, Any]:
        return {name: getattr(self, name) for name in _BINDING_FIELDS}


def _identity_projection(identity: Any, side: str) -> Mapping[str, Any]:
    """観測 object から artifact に入れる値だけを厳密に射影する。"""

    match_count = _exact_int(
        getattr(identity, "match_count", None), f"{side} match count"
    )
    if match_count != 1:
        raise ValueError(
            "identical function identity requires exactly one name match per side"
        )
    return {
        "executable_sha256": _exact_text(
            getattr(identity, "executable_sha256", None), f"{side} executable SHA-256"
        ).lower(),
        "function_name": _exact_text(
            getattr(identity, "function_name", None), f"{side} function name"
        ),
        "language_id": _exact_text(
            getattr(identity, "language_id", None), f"{side} language ID"
        ),
        "compiler_spec_id": _exact_text(
            getattr(identity, "compiler_spec_id", None), f"{side} compiler spec ID"
        ),
        "image_base": _exact_int(
            getattr(identity, "image_base", None), f"{side} image base"
        ),
        "entry": _exact_address(getattr(identity, "entry", None), f"{side} entry"),
        "body_range": (
            _exact_address(
                (getattr(identity, "body_range", None) or (None, None))[0],
                f"{side} body start",
            ),
            _exact_address(
                (getattr(identity, "body_range", None) or (None, None))[1],
                f"{side} body end",
            ),
        ),
        "match_count": match_count,
    }


@dataclass(frozen=True)
class IdenticalFunctionIdentityProofArtifact:
    """左右一致した identity 観測と、その実行への束縛を封じた proof。"""

    schema: str
    # `body` は dict なので比較・hash からは外す（frozen dataclass が
    # unhashable にならないように）。`artifact_digest` が body を決めていて、
    # 食い違いは `validate()` が検出する。
    body: Mapping[str, Any] = field(compare=False)
    artifact_digest: str

    @classmethod
    def create(
        cls,
        left: Any,
        right: Any,
        *,
        session_binding: IdenticalFunctionIdentitySessionBinding,
    ) -> "IdenticalFunctionIdentityProofArtifact":
        if type(session_binding) is not IdenticalFunctionIdentitySessionBinding:
            raise ValueError("identical function identity session binding is not exact")
        left_projection = _identity_projection(left, "left")
        right_projection = _identity_projection(right, "right")
        if left_projection != right_projection:
            raise ValueError("identical function identity observations differ")
        if left_projection["function_name"] != session_binding.function_name:
            raise ValueError(
                "identical function identity function name differs from the session"
            )
        if left_projection["executable_sha256"] != _content_identity_sha256(
            session_binding.binary_content_identity
        ):
            raise ValueError(
                "observed executable SHA-256 differs from the session input identity"
            )
        body = {
            "schema": IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA,
            **session_binding.as_body_fields(),
            **{name: left_projection[name] for name in _IDENTITY_FIELDS},
        }
        return cls(
            schema=IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA,
            body=body,
            artifact_digest=authority_digest(body),
        )

    def validate(self) -> bool:
        if (
            self.schema != IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA
            or not isinstance(self.body, Mapping)
            or self.body.get("schema") != IDENTICAL_FUNCTION_IDENTITY_PROOF_SCHEMA
            or set(self.body) != {"schema", *_BINDING_FIELDS, *_IDENTITY_FIELDS}
        ):
            return False
        return authority_digest(dict(self.body)) == self.artifact_digest


@dataclass(frozen=True, init=False)
class IdenticalFunctionIdentitySignal:
    """artifact から発行される decisive producer signal。"""

    proof_artifact_digest: str
    producer_id: str
    artifact: IdenticalFunctionIdentityProofArtifact = field(repr=False, compare=False)

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _SIGNAL_TOKEN:
            raise TypeError(
                "identical function identity signal must be issued from its artifact"
            )
        for name in ("proof_artifact_digest", "producer_id", "artifact"):
            object.__setattr__(self, name, values.pop(name))
        if values:
            raise TypeError("identical function identity signal fields are not sealed")
        if not self.validates():
            raise ValueError("identical function identity signal authority is invalid")

    @classmethod
    def from_artifact(
        cls, artifact: IdenticalFunctionIdentityProofArtifact,
    ) -> "IdenticalFunctionIdentitySignal":
        if type(artifact) is not IdenticalFunctionIdentityProofArtifact:
            raise ValueError("identical function identity artifact is not exact")
        return cls(
            proof_artifact_digest=artifact.artifact_digest,
            producer_id=IDENTICAL_FUNCTION_IDENTITY_PRODUCER_ID,
            artifact=artifact,
            _factory_token=_SIGNAL_TOKEN,
        )

    def validates(self) -> bool:
        return bool(
            type(self.artifact) is IdenticalFunctionIdentityProofArtifact
            and self.artifact.validate()
            and self.proof_artifact_digest == self.artifact.artifact_digest
            and self.producer_id == IDENTICAL_FUNCTION_IDENTITY_PRODUCER_ID
        )

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        if not self.validates():
            raise ValueError("identical function identity signal authority is invalid")
        return dict(self.artifact.body)


class IdenticalFunctionIdentityPilotEncoder:
    """artifact が「この実行のこの pair」のものだと確認してから 1 回だけ出す。"""

    @staticmethod
    def _session_binding(session: Any) -> IdenticalFunctionIdentitySessionBinding:
        from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
            _operational_binary_content_identity,
        )

        payload = dict(session.execution_payload or ())
        left_identity = _operational_binary_content_identity(
            payload.get("binary1_content_identity")
        )
        right_identity = _operational_binary_content_identity(
            payload.get("binary2_content_identity")
        )
        if left_identity != right_identity:
            raise ValueError(
                "identical function identity requires one shared session input identity"
            )
        function_name1 = _exact_text(payload.get("function_name1"), "session function 1")
        if function_name1 != payload.get("function_name2"):
            raise ValueError("identical function identity session function names differ")
        return IdenticalFunctionIdentitySessionBinding(
            result_occurrence_id=session.identity.result_occurrence_id,
            execution_identity_digest=session.identity.execution_identity_digest,
            left_binary_id=_exact_text(payload.get("binary1_id"), "session binary 1 ID"),
            right_binary_id=_exact_text(payload.get("binary2_id"), "session binary 2 ID"),
            binary_content_identity=left_identity,
            function_name=function_name1,
            observation_contract_id=_exact_text(
                payload.get("observation_contract_id"), "session observation contract"
            ),
        )

    def _verified_digest(self, session: Any, signal: Any) -> str:
        if not signal.validates():
            raise ValueError("identical function identity signal is not validated")
        artifact = signal.artifact
        expected = self._session_binding(session).as_body_fields()
        actual = {name: artifact.body.get(name) for name in _BINDING_FIELDS}
        if actual != dict(expected):
            raise ValueError(
                "identical function identity artifact is not bound to this execution"
            )
        if authority_digest(dict(artifact.body)) != signal.proof_artifact_digest:
            raise ValueError("identical function identity artifact digest differs")
        return signal.proof_artifact_digest

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        if type(signal) is not IdenticalFunctionIdentitySignal:
            return ()
        digest = self._verified_digest(session, signal)
        committed = session.domain_signal_state.get(
            IDENTICAL_FUNCTION_IDENTITY_COMMITTED_KEY
        )
        if committed is not None:
            if committed != digest:
                raise ValueError(
                    "a different identical function identity proof was already committed"
                )
            return ()
        return (EventIntent(
            EventType.EQ_CLOSURE, DecisiveProofEventAuthority(digest),
        ),)

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...],
    ) -> None:
        if type(signal) is not IdenticalFunctionIdentitySignal:
            return
        exact = tuple(intents)
        committed = session.domain_signal_state.get(
            IDENTICAL_FUNCTION_IDENTITY_COMMITTED_KEY
        )
        if not exact:
            if committed != signal.proof_artifact_digest:
                raise ValueError(
                    "identical function identity emission transaction is invalid"
                )
            return
        if len(exact) != 1 or exact[0].event_type is not EventType.EQ_CLOSURE:
            raise ValueError("identical function identity emission transaction is invalid")
        if committed is not None:
            raise ValueError("identical function identity proof was already committed")
        session.domain_signal_state[
            IDENTICAL_FUNCTION_IDENTITY_COMMITTED_KEY
        ] = self._verified_digest(session, signal)
