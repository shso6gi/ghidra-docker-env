# -*- coding: utf-8 -*-
"""記録済み corpus の manifest と、集計契約（Issue #109）。

この module が持つのは 2 つだけ:

1. **どの replay が存在し、どれが PR gate の対象か**（`cases.json` が正本。
   test 名の文字列一致や `-k` の羅列に依存しない）。
2. **corpus 全体としての完全性と時間予算**（欠落・重複・予算超過の判定）。

(2) の実装はここ 1 箇所しかない。1 process で 9 replay を回す実行でも、
matrix で 1 shard 1 replay に割った実行でも、同じ
:func:`validate_corpus` が同じ規則で判定する。serial 用と matrix 用で
別々に書くと、片方だけ緩い完全性検査になりうる。

ここは test 基盤であって、checker にも判定 authority にも入力を渡さない。
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

FIXTURE_ROOT = Path(__file__).resolve().parent
CASES_FILE = FIXTURE_ROOT / "cases.json"

CASES_SCHEMA = "recorded-pcode-cases-v1"
REPLAY_RECORD_SCHEMA = "recorded-pair-replay-record-v1"

VARIANT_DEFAULT = "default"
VARIANT_FAST_PATH_ON = "fast_path_on"
VARIANT_FAST_PATH_OFF = "fast_path_off"

#: variant → `identical_fast_path`。``None`` は「記録時の mode を使う」。
VARIANT_FAST_PATH = {
    VARIANT_DEFAULT: None,
    VARIANT_FAST_PATH_ON: True,
    VARIANT_FAST_PATH_OFF: False,
}

#: variant → replay worker の ``--fast-path``。
WORKER_FAST_PATH = {
    VARIANT_DEFAULT: "recorded",
    VARIANT_FAST_PATH_ON: "on",
    VARIANT_FAST_PATH_OFF: "off",
}

#: 選択の単位。``pr_gate`` は PR ごとに走る集合、``full`` は corpus 全体。
TIER_PR_GATE = "pr_gate"
TIER_FULL = "full"
TIERS = (TIER_PR_GATE, TIER_FULL)


class CorpusContractViolation(AssertionError):
    """corpus 全体としての契約（完全性・予算）が破れた。"""


class CorpusManifestInvalid(ValueError):
    """`cases.json` を読めない / 形が違う。skip せず落とす。"""


@dataclass(frozen=True)
class ReplaySpec:
    """1 回分の replay。case と variant の組で一意。"""

    case_id: str
    variant: str
    budget_seconds: int
    pr_gate: bool

    @property
    def variant_id(self) -> str:
        """人にも CI の matrix にも使う安定 id。"""

        if self.variant == VARIANT_DEFAULT:
            return self.case_id
        return "{}.{}".format(self.case_id, self.variant)


@dataclass(frozen=True)
class ReplayRecord:
    """1 replay の実行結果。集計はこれだけを見る。"""

    case_id: str
    variant: str
    seconds: float
    outcome: str

    @property
    def variant_id(self) -> str:
        if self.variant == VARIANT_DEFAULT:
            return self.case_id
        return "{}.{}".format(self.case_id, self.variant)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema": REPLAY_RECORD_SCHEMA,
            "case_id": self.case_id,
            "variant": self.variant,
            "variant_id": self.variant_id,
            "seconds": round(float(self.seconds), 3),
            "outcome": self.outcome,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ReplayRecord":
        if payload.get("schema") != REPLAY_RECORD_SCHEMA:
            raise CorpusContractViolation(
                "unexpected replay record schema: " + repr(payload.get("schema"))
            )
        for name in ("case_id", "variant", "outcome"):
            if not isinstance(payload.get(name), str) or not payload[name]:
                raise CorpusContractViolation(
                    "replay record field {} is missing".format(name)
                )
        if not isinstance(payload.get("seconds"), (int, float)):
            raise CorpusContractViolation("replay record has no seconds")
        return cls(
            case_id=payload["case_id"], variant=payload["variant"],
            seconds=float(payload["seconds"]), outcome=payload["outcome"],
        )


def load_manifest() -> Mapping[str, Any]:
    """`cases.json` を読む。壊れていたら落ちる（既定値で続けない）。"""

    try:
        payload = json.loads(CASES_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise CorpusManifestInvalid(
            "the recorded corpus manifest could not be read: " + str(exc)
        ) from exc
    if payload.get("schema") != CASES_SCHEMA:
        raise CorpusManifestInvalid(
            "unexpected recorded-pair cases schema: " + repr(payload.get("schema"))
        )
    if not isinstance(payload.get("cases"), list) or not payload["cases"]:
        raise CorpusManifestInvalid("recorded-pair cases.json has no cases")
    if type(payload.get("corpus_budget_seconds")) is not int:
        raise CorpusManifestInvalid(
            "recorded-pair cases.json has no corpus_budget_seconds"
        )
    return payload


MANIFEST = load_manifest()
CORPUS_BUDGET_SECONDS: int = MANIFEST["corpus_budget_seconds"]
CASES: Dict[str, Mapping[str, Any]] = {
    case["case_id"]: case for case in MANIFEST["cases"]
}


def _spec(case: Mapping[str, Any], variant: str) -> ReplaySpec:
    if type(case.get("pr_gate")) is not bool:
        raise CorpusManifestInvalid(
            "{}: pr_gate must be an exact bool".format(case.get("case_id"))
        )
    if variant not in VARIANT_FAST_PATH:
        raise CorpusManifestInvalid(
            "{}: unknown variant {!r}".format(case.get("case_id"), variant)
        )
    return ReplaySpec(
        case_id=case["case_id"], variant=variant,
        budget_seconds=int(case["budget_seconds"]), pr_gate=bool(case["pr_gate"]),
    )


ALL_REPLAYS: Tuple[ReplaySpec, ...] = tuple(
    _spec(case, variant)
    for case in MANIFEST["cases"]
    for variant in case["variants"]
)
PR_GATE_REPLAYS: Tuple[ReplaySpec, ...] = tuple(
    spec for spec in ALL_REPLAYS if spec.pr_gate
)


def replays_for_tier(tier: str) -> Tuple[ReplaySpec, ...]:
    if tier == TIER_FULL:
        return ALL_REPLAYS
    if tier == TIER_PR_GATE:
        return PR_GATE_REPLAYS
    raise CorpusManifestInvalid("unknown recorded corpus tier: " + repr(tier))


def select_replays(
    *, tier: str = TIER_PR_GATE, variant_ids: Sequence[str] = (),
) -> Tuple[ReplaySpec, ...]:
    """走らせる replay を決める。

    ``variant_ids`` を渡すと tier を無視してその id だけを返す（matrix の
    1 shard 用）。存在しない id は黙って無視せず落とす: shard が何も走らずに
    成功すると、aggregate から見て「通った」と読めてしまう。
    """

    if not variant_ids:
        return replays_for_tier(tier)
    by_id = {spec.variant_id: spec for spec in ALL_REPLAYS}
    unknown = [name for name in variant_ids if name not in by_id]
    if unknown:
        raise CorpusManifestInvalid(
            "no such recorded replay: {} (known: {})".format(
                ", ".join(sorted(unknown)), ", ".join(sorted(by_id))
            )
        )
    # 指定順ではなく manifest 順に正規化して、重複指定も 1 回に畳む。
    wanted = set(variant_ids)
    return tuple(spec for spec in ALL_REPLAYS if spec.variant_id in wanted)


# ---------------------------------------------------------------------------
# corpus 全体の契約（完全性 + 予算）。実装はここだけ。
# ---------------------------------------------------------------------------


def validate_corpus(
    records: Iterable[ReplayRecord],
    *,
    expected: Sequence[ReplaySpec],
    budget_seconds: Optional[int] = CORPUS_BUDGET_SECONDS,
) -> List[str]:
    """期待した replay が過不足なく 1 回ずつ成功し、合計が予算内であること。

    fail-closed: 欠落・重複・想定外・失敗・予算超過はすべて
    :class:`CorpusContractViolation`。「artifact が無い」を「走らなくてよかった」
    と読む余地は残さない。

    予算は **各 replay の測定時間の合計**に対して掛ける。matrix で並列に
    流したときの workflow wall-clock ではない（並列化は所要を短くするが、
    Issue #109 の時間 AC が意味するものを変えない）。

    戻り値は報告用の行。判定はこの関数の例外が持ち、行は何も決めない。
    """

    expected_ids = [spec.variant_id for spec in expected]
    if len(set(expected_ids)) != len(expected_ids):
        raise CorpusContractViolation(
            "the expected replay set itself has duplicates: " + repr(expected_ids)
        )

    seen: Dict[str, List[ReplayRecord]] = {}
    for record in records:
        seen.setdefault(record.variant_id, []).append(record)

    missing = sorted(set(expected_ids) - set(seen))
    if missing:
        raise CorpusContractViolation(
            "{} of {} replays produced no result: {}. A missing result is a "
            "failure, never a pass.".format(
                len(missing), len(expected_ids), ", ".join(missing)
            )
        )
    unexpected = sorted(set(seen) - set(expected_ids))
    if unexpected:
        raise CorpusContractViolation(
            "results arrived for replays that were not expected: "
            + ", ".join(unexpected)
        )
    duplicated = sorted(name for name, rows in seen.items() if len(rows) != 1)
    if duplicated:
        raise CorpusContractViolation(
            "these replays reported more than once, so the total cannot be "
            "trusted: " + ", ".join(duplicated)
        )
    failed = sorted(
        name for name, rows in seen.items() if rows[0].outcome != "passed"
    )
    if failed:
        raise CorpusContractViolation(
            "these replays did not pass: "
            + ", ".join(
                "{}={}".format(name, seen[name][0].outcome) for name in failed
            )
        )

    ordered = sorted(
        (seen[name][0] for name in expected_ids),
        key=lambda record: -record.seconds,
    )
    total = sum(record.seconds for record in ordered)
    lines = format_summary(ordered, total=total, budget_seconds=budget_seconds)
    if budget_seconds is not None and total > budget_seconds:
        raise CorpusContractViolation(
            "the recorded corpus took {:.1f}s, over the {}s budget (Issue #109 "
            "time acceptance criterion, revised 2026-09-17, measured as the sum "
            "of the replay times): {}. Do not drop cases, trim the recorded "
            "surface, or turn a harness timeout into an UNKNOWN to fit it."
            .format(
                total, budget_seconds,
                ", ".join(
                    "{}={:.1f}s".format(record.variant_id, record.seconds)
                    for record in ordered
                ),
            )
        )
    return lines


def format_summary(
    records: Sequence[ReplayRecord], *, total: Optional[float] = None,
    budget_seconds: Optional[int] = None,
) -> List[str]:
    """報告用の compact な表。判定には関与しない。"""

    if total is None:
        total = sum(record.seconds for record in records)
    width = max([len(record.variant_id) for record in records] + [len("TOTAL")])
    header = (
        "recorded corpus wall clock -- {} replays, Issue #109 time criterion "
        "(revised 2026-09-17; the sum below, not a parallel workflow's clock)"
    ).format(len(records))
    lines = [header]
    for record in records:
        case = CASES.get(record.case_id) or {}
        lines.append("  {:<{width}}  {:8.2f}s  (case budget {}s)".format(
            record.variant_id, record.seconds,
            case.get("budget_seconds", "?"), width=width,
        ))
    budget = "" if budget_seconds is None else "  (corpus budget {}s)".format(
        budget_seconds
    )
    lines.append("  {:<{width}}  {:8.2f}s{}".format(
        "TOTAL", total, budget, width=width,
    ))
    return lines


__all__ = [
    "ALL_REPLAYS",
    "CASES",
    "CASES_FILE",
    "CASES_SCHEMA",
    "CORPUS_BUDGET_SECONDS",
    "CorpusContractViolation",
    "CorpusManifestInvalid",
    "FIXTURE_ROOT",
    "MANIFEST",
    "PR_GATE_REPLAYS",
    "REPLAY_RECORD_SCHEMA",
    "ReplayRecord",
    "ReplaySpec",
    "TIERS",
    "TIER_FULL",
    "TIER_PR_GATE",
    "VARIANT_DEFAULT",
    "VARIANT_FAST_PATH",
    "VARIANT_FAST_PATH_OFF",
    "VARIANT_FAST_PATH_ON",
    "WORKER_FAST_PATH",
    "format_summary",
    "load_manifest",
    "replays_for_tier",
    "select_replays",
    "validate_corpus",
]
