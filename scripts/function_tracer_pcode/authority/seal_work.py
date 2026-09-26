"""canonical result finalization bundle を作る・確かめる仕事の作業量（Issue #110）の唯一の owner。

封印（`build_canonical_result_finalization_bundle`）・検証（`validate_canonical_result_finalization_bundle`）・
supervisor の封印・永続化（`persist_canonical_result_envelope`）は、sealed event stream・lifecycle
projection・receipt・preimage の大きさに比例する仕事（event の列挙・codec の encode / decode・
canonicalization・hash chain の検証・reducer の replay・digest・bundle の構築）をする。これらは
**呼ぶ側が渡す有限の作業量 `work`（`SealWork`）の中でだけ** 行う:

1. 最初に入力の大きさを `authority/canonical_units` の meter で **数えながら** 測る（`SealPlan.price`）。
   stream の event の数と大きさは `authority/event_contract` の契約と比べ、外なら 1 つも作らずに止まる。
2. 各段（`SEAL_COST_MODEL` の 1 行）は **実行する前に** その段の仕事量を `plan.charge(段)` で数える。
   段の仕事量は測った大きさの線形結合で、表はこの module の 1 か所だけにある。
3. 作業量を超えたら `BundleWorkExceeded`（型付きの失敗）。部分的な bundle・digest・replay は返さない。

上限の内側では、数えるだけで bundle / receipt / digest / 永続化した表現の byte 列は変わらない。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.authority.canonical_units import (
    UnitSink,
    measure_canonical_units,
)
from scripts.function_tracer_pcode.authority.event_contract import (
    AUTHORITY_EVENT_CONTRACT,
    AuthorityEventContract,
)


class BundleWorkExceeded(ValueError):
    """封印・検証の仕事が作業量を超えた、または入力が authority event の契約の外（部分的な結果は無い）。

    `kind` は `"work"`（作業量の上限）か `"contract"`（入力が契約の外）。`ValueError` の subclass:
    永続化した bundle を読む側（supervisor の terminal snapshot・reporting）は、検証できない bundle と
    同じく無効として扱う。封印する側の CLI（`cli/commands/equivalence`）は受けずに伝える: worker は
    canonical result envelope を書かずに失敗で終わり、supervisor が pair を operational ERROR として
    確定する（部分的な bundle を使わない）。判定の receipt を残した結果の ERROR にするのは出力の
    finalization（PR #190 の `AuthoritySeal`）の責務。
    """

    def __init__(self, message: str, *, kind: str, step: str, consumed: int, limit: Optional[int]) -> None:
        super().__init__(message)
        self.kind = kind
        self.step = step
        self.consumed = consumed
        self.limit = limit


class SealWork(UnitSink):
    """封印の作業量の protocol: `charge(units)`（超えれば `BundleWorkExceeded`）・`remaining()` と、
    この作業量で封印してよい preimage の上限 `preimage_limit`（canonical unit）。"""

    preimage_limit: int

    def remaining(self) -> Optional[int]:  # pragma: no cover - protocol
        raise NotImplementedError


class SealWorkBudget(SealWork):
    """有限の封印の作業量（上限は必ず渡す: 上限なしの封印は作れない）。"""

    __slots__ = ("limit", "consumed", "step", "preimage_limit")

    def __init__(
        self, limit: int, *, preimage_limit: int = AUTHORITY_EVENT_CONTRACT.max_result_preimage_units,
    ) -> None:
        if type(limit) is not int or limit < 0:
            raise ValueError("a seal work budget has a finite non-negative limit")
        if type(preimage_limit) is not int or preimage_limit < 0:
            raise ValueError("a seal work budget has a finite non-negative preimage bound")
        self.limit = limit
        self.consumed = 0
        self.preimage_limit = preimage_limit
        #: 今数えている段（失敗の報告用）
        self.step = "price"

    @classmethod
    def for_seal(
        cls, *, preimage_units: int,
        contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
    ) -> "SealWorkBudget":
        """契約の上限の stream と、上限 `preimage_units` の preimage を封印・検証・永続化できる作業量。

        上限の内側の入力で封印が作業量の不足で失敗しない（決定的: 同じ入力なら同じ量を数える）。
        preimage はこの上限の中でだけ封印する（`SealPlan.price` が測りながら強制する）。
        """

        return cls(
            seal_work_limit(contract=contract, preimage_units=preimage_units),
            preimage_limit=preimage_units,
        )

    @classmethod
    def for_result(
        cls, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
    ) -> "SealWorkBudget":
        """結果の payload 全体を preimage にする呼び出し側（CLI・結果の検証・reporting）の作業量。"""

        return cls.for_seal(preimage_units=contract.max_result_preimage_units, contract=contract)

    @classmethod
    def for_supervisor(
        cls, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
    ) -> "SealWorkBudget":
        """supervisor の terminal の封印（固定の形の preimage）の作業量。"""

        return cls.for_seal(preimage_units=contract.max_supervisor_preimage_units, contract=contract)

    def remaining(self) -> Optional[int]:
        return self.limit - self.consumed

    def charge(self, units: int) -> None:
        if type(units) is not int or units < 0:
            raise ValueError("seal work is charged in non-negative int units")
        self.consumed += units
        if self.consumed > self.limit:
            raise BundleWorkExceeded(
                f"seal work exceeded {self.limit} units at {self.step}",
                kind="work", step=self.step, consumed=self.consumed, limit=self.limit,
            )


#: 封印・検証・永続化の各段の仕事量（測った大きさの成分ごとの係数）。**表はここだけ**。
#:
#: 成分: `stream`（event の payload と header の単位）・`events`（event の数）・`projection`（lifecycle
#: projection の単位）・`receipts`（decisive / timeout / error / decision / occurrence / selection
#: receipt の単位）・`preimage`（結果の payload の preimage の単位）・`execution`（execution payload の
#: 単位）・`reduction`（reducer の replay: 実行 event × active な occurrence）・`bundle`（封印した bundle
#: 全体の単位 = 上の和）。係数は各段が値全体を辿る回数（canonicalize・書く・読む・hash chain の検証は
#: それぞれ 1 回）。
SEAL_COST_MODEL: Dict[str, Mapping[str, int]] = {
    # 封印（production）
    "pilot_validate": {"stream": 2, "events": 4, "projection": 2, "receipts": 1},
    "semantic_projection": {"projection": 2, "execution": 2},
    "execution_payload_digest": {"execution": 2},
    "encode_stream": {"stream": 4, "events": 1},
    "encode_projection": {"projection": 4},
    "encode_receipts": {"receipts": 4},
    "preimage_digest": {"preimage": 2},
    "bundle_digest": {"bundle": 2},
    # 封印（supervisor の terminal stream）
    "supervisor_stream_validate": {"stream": 2, "events": 1},
    "supervisor_replay": {"stream": 2, "events": 2, "reduction": 1, "projection": 2},
    # 検証（bundle の dict）
    "verify_bundle_digest": {"bundle": 2},
    "verify_preimage_digest": {"preimage": 2},
    "decode_stream": {"stream": 7, "events": 2},
    "decode_projection": {"projection": 5},
    "decode_receipts": {"receipts": 5},
    "verify_replay": {"stream": 2, "events": 2, "reduction": 1, "projection": 2},
    "verify_dual_write_replay": {"stream": 2, "events": 4, "reduction": 1, "projection": 2},
    "verify_timeout_selection": {"stream": 6, "events": 6, "reduction": 1, "projection": 2},
    "verify_equality": {"projection": 1, "receipts": 1},
    "verify_execution_identity": {"execution": 4, "receipts": 2},
    "verify_decisive_provenance": {"preimage": 1},
    "verify_semantic_projection": {"projection": 2, "execution": 2, "preimage": 1},
    # 永続化（結果の payload 全体 = preimage + bundle）
    "persist_project": {"preimage": 2, "bundle": 2},
    "persist_surface": {"preimage": 2, "bundle": 2},
    "persist_seal": {"preimage": 2, "bundle": 2},
    "persist_write": {"preimage": 1, "bundle": 1},
}

@dataclass(frozen=True)
class SealComponents:
    """測った入力の大きさ（canonical unit）。"""

    stream: int
    events: int
    projection: int
    receipts: int
    preimage: int
    execution: int
    reduction: int
    #: bundle の固定の包み（`AuthorityEventContract.bundle_frame_units`）
    frame: int

    @property
    def bundle(self) -> int:
        return self.stream + self.projection + self.receipts + self.execution + self.frame

    def get(self, name: str) -> int:
        return self.bundle if name == "bundle" else getattr(self, name)


class SealPlan:
    """1 回の封印・検証の作業量の計画（測った大きさと、段ごとに 1 回だけ数える記録）。"""

    __slots__ = ("work", "components", "charged", "contract")

    def __init__(
        self, work: SealWork, components: SealComponents,
        contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
    ) -> None:
        self.work = work
        self.components = components
        self.contract = contract
        #: 数え終えた段（同じ段を 2 回数えない: exact-once）
        self.charged: list = []

    @classmethod
    def price(
        cls, work: Any, *, stream: Any, projection: Any, receipts: Sequence[Any],
        preimage: Any, execution: Any,
        contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
    ) -> "SealPlan":
        """入力の大きさを `work` へ数えながら測り、契約の上限と比べる（外なら何も作らずに止まる）。

        `stream` は sealed event stream（object）か、bundle の中の encode 済みの dict。event は 1 つ
        ずつ（header・digest を含む全体を）辿る前に数え、数えた量が上限を超えた時点で止まる。
        preimage は `work.preimage_limit` まで。最後に replay の見積もりを数える。
        """

        _require_work(work)
        measured = _measure_parts(
            work, contract, stream=stream, projection=projection, receipts=receipts,
            execution=execution,
        )
        preimage_units = _measure_capped(
            preimage, work, work.preimage_limit, "the result preimage is outside its seal bound",
        )
        # replay の仕事は event ごとに、それまでに観測した occurrence（discharge 済みも含む）に比例する:
        # 最後の `c_active_base` ではなく stream の cause event の数で見積もる（projection の有無に依らない）
        reduction = measured["events"] * max(1, measured["cause_events"])
        work.charge(reduction)
        components = SealComponents(
            stream=measured["stream"], events=measured["events"],
            projection=measured["projection"], receipts=measured["receipts"],
            preimage=preimage_units, execution=measured["execution"], reduction=reduction,
            frame=contract.bundle_frame_units,
        )
        return cls(work, components, contract)

    def check_sealed_form(
        self, *, stream: Any, projection: Any, receipts: Sequence[Any], execution: Any,
    ) -> None:
        """encode した形（読む側が測る形）が契約の上限の中か、digest を取る前に数えながら確かめる。

        書く側（封印）は object の形で `price` を測るが、読む側（`validate_...`）は encode した dict を
        測る。書いた bundle を読む側が拒まないよう、同じ上限を encode した形でも確かめる（replay の
        見積もりは数えない: 同じ replay を 2 回数えない）。
        """

        _measure_parts(
            self.work, self.contract, stream=stream, projection=projection, receipts=receipts,
            execution=execution,
        )

    def measure_more(self, *, projection: Any = None, receipts: Sequence[Any] = ()) -> None:
        """replay の後にできた projection / receipt を、encode する前に数えながら測って足す。

        足した後の大きさも契約の上限と比べる（`price` と同じ上限: 超えた時点で止まる）。
        """

        contract = self.contract
        current = self.components
        projection_units = current.projection
        if projection is not None:
            projection_units += _measure_capped(
                projection, self.work, contract.max_projection_units - current.projection,
                "the lifecycle projection is outside the authority event contract",
            )
        receipt_units = current.receipts + _measure_capped(
            tuple(receipts), self.work, contract.max_receipt_units - current.receipts,
            "the receipts are outside the authority event contract",
        ) if receipts else current.receipts
        self.components = SealComponents(
            stream=current.stream, events=current.events,
            projection=projection_units, receipts=receipt_units,
            preimage=current.preimage, execution=current.execution,
            reduction=current.reduction, frame=current.frame,
        )

    def cost(self, step: str) -> int:
        coefficients = SEAL_COST_MODEL[step]
        return sum(weight * self.components.get(name) for name, weight in coefficients.items())

    def charge(self, step: str) -> None:
        """段 `step` を実行する **前** に、その段の仕事量を 1 回だけ数える。"""

        if step not in SEAL_COST_MODEL:
            raise KeyError(f"unregistered seal step: {step}")
        if step in self.charged:
            raise ValueError(f"seal step {step} is charged twice")
        if hasattr(self.work, "step"):
            self.work.step = step
        self.work.charge(self.cost(step))
        self.charged.append(step)


def seal_work_limit(
    *, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT, preimage_units: int,
) -> int:
    """契約の上限の入力を封印し、検証し、永続化する作業量の上限（測る分 + 全段の和、封印と永続化の 2 回分）。

    成分の上限は全部 `authority/event_contract` の契約（`SealPlan.price` が測りながら強制する）と
    呼ぶ側の preimage の上限だけから導く: 契約の内側の入力は作業量の不足で失敗しない。測る分は
    object の形（`price`）と encode した形（`check_sealed_form`）の 2 回。
    """

    if type(preimage_units) is not int or preimage_units < 0:
        raise ValueError("a seal work limit needs a non-negative preimage bound")
    worst = SealComponents(
        stream=contract.max_sealed_stream_units, events=contract.max_sealed_events,
        projection=contract.max_projection_units, receipts=contract.max_receipt_units,
        preimage=preimage_units, execution=contract.max_execution_payload_units,
        reduction=contract.max_sealed_events * contract.max_cause_occurrences,
        frame=contract.bundle_frame_units,
    )
    measured_parts = worst.stream + worst.projection + worst.receipts + worst.execution
    priced = 2 * measured_parts + worst.preimage + worst.reduction
    steps = sum(
        sum(weight * worst.get(name) for name, weight in coefficients.items())
        for coefficients in SEAL_COST_MODEL.values()
    )
    return 2 * (priced + steps)


def persisted_envelope_byte_limit(
    *, contract: AuthorityEventContract = AUTHORITY_EVENT_CONTRACT,
    preimage_units: Optional[int] = None,
) -> int:
    """永続化した canonical result envelope の byte 数の上限（preimage + 契約の上限の bundle）。

    canonical unit は UTF-8 の JSON の byte 以上。envelope の file は ASCII の escape（非 ASCII の 1 文字が
    `\\uXXXX` の 6〜12 byte、UTF-8 の 2〜4 byte の高々 3 倍）で書くので、封印した形の倍率を掛ける。
    書く側（`persist_canonical_result_envelope`）はこの上限を超える envelope を書かない。
    """

    preimage = contract.max_result_preimage_units if preimage_units is None else preimage_units
    return contract.sealed_form_factor * (
        preimage + contract.max_sealed_stream_units + contract.max_projection_units
        + contract.max_receipt_units + contract.max_execution_payload_units
        + contract.bundle_frame_units
    )


def _require_work(work: Any) -> None:
    if not isinstance(work, SealWork):
        raise TypeError("sealing requires a finite SealWork budget")


class _Capped(UnitSink):
    """`work` へ数えながら、この部分の上限 `cap` も数える（超えた時点で契約の外として止まる）。"""

    __slots__ = ("work", "cap", "used", "message")

    def __init__(self, work: Any, cap: int, message: str) -> None:
        self.work, self.cap, self.used, self.message = work, cap, 0, message

    def charge(self, units: int) -> None:
        self.work.charge(units)
        self.used += units
        if self.used > self.cap:
            _contract(self.work, self.message, self.cap)


def _measure_capped(value: Any, work: Any, cap: int, message: str) -> int:
    return measure_canonical_units(value, _Capped(work, cap, message))


def _measure_parts(
    work: Any, contract: AuthorityEventContract, *, stream: Any, projection: Any,
    receipts: Sequence[Any], execution: Any,
) -> Dict[str, int]:
    """stream（event ごと）・projection・receipt・execution payload を、各上限まで数えながら測る。"""

    events = _stream_events(stream)
    if len(events) > contract.max_sealed_events:
        _contract(work, f"sealed event stream has {len(events)} events", contract.max_sealed_events)
    stream_sink = _Capped(
        work, contract.max_sealed_stream_units,
        "the sealed event stream is outside the authority event contract",
    )
    stream_units = measure_canonical_units(_stream_frame(stream), stream_sink)
    cause_events = 0
    for event in events:
        stream_units += measure_canonical_units(_event_value(event), stream_sink)
        if _is_cause_event(event):
            cause_events += 1
            if cause_events > contract.max_cause_occurrences:
                _contract(work, "the sealed event stream has more causes than the contract",
                          contract.max_cause_occurrences)
    projection_units = _measure_capped(
        projection, work, contract.max_projection_units,
        "the lifecycle projection is outside the authority event contract",
    )
    receipt_units = _measure_capped(
        tuple(receipts), work, contract.max_receipt_units,
        "the receipts are outside the authority event contract",
    )
    execution_units = _measure_capped(
        execution, work, contract.max_execution_payload_units,
        "the execution payload is outside the authority event contract",
    )
    return {
        "stream": stream_units, "events": len(events), "cause_events": cause_events,
        "projection": projection_units, "receipts": receipt_units, "execution": execution_units,
    }


def _stream_events(stream: Any) -> Sequence[Any]:
    if isinstance(stream, Mapping):
        payload = stream.get("payload")
        events = payload.get("events") if isinstance(payload, Mapping) else None
        if not isinstance(events, (list, tuple)):
            raise ValueError("encoded sealed event stream lacks events")
        return events
    events = getattr(stream, "events", None)
    if not isinstance(events, tuple):
        raise TypeError("sealed event stream lacks an events tuple")
    return events


def _event_value(event: Any) -> Any:
    """測る event の全体（header・digest・payload）。記録済みの event は object、bundle の中は dict。"""

    if isinstance(event, Mapping) or hasattr(event, "header"):
        return event
    return (getattr(event, "authority_payload", None), getattr(event, "diagnostic_payload", None))


def _stream_frame(stream: Any) -> Any:
    """stream の event 以外（envelope・schema の包み）。"""

    if isinstance(stream, Mapping):
        payload = stream.get("payload")
        frame = {key: value for key, value in stream.items() if key != "payload"}
        if isinstance(payload, Mapping):
            frame["payload"] = {key: value for key, value in payload.items() if key != "events"}
        return frame
    return getattr(stream, "envelope", None)


def _contract(work: Any, message: str, limit: int) -> None:
    raise BundleWorkExceeded(
        message, kind="contract", step="price", consumed=getattr(work, "consumed", 0), limit=limit,
    )


def _is_cause_event(event: Any) -> bool:
    """cause occurrence を作る event か（記録済みの event は object、bundle の中は encode 済みの dict）。"""

    from scripts.function_tracer_pcode.authority.lifecycle.stream import EventType

    if isinstance(event, Mapping):
        header = event.get("header")
        return isinstance(header, Mapping) and header.get("event_type") == EventType.CAUSE_OBSERVED.value
    header = getattr(event, "header", None)
    return getattr(header, "event_type", None) is EventType.CAUSE_OBSERVED


__all__ = [
    "persisted_envelope_byte_limit",
    "BundleWorkExceeded",
    "SEAL_COST_MODEL",
    "SealComponents",
    "SealPlan",
    "SealWork",
    "SealWorkBudget",
    "seal_work_limit",
]
