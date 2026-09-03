"""Lossless legacy ingestion isolated from strict v2 authority."""

from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Optional


class LegacyMappingCertainty(str, Enum):
    EXACT = "EXACT"
    UMBRELLA = "UMBRELLA"
    AMBIGUOUS = "AMBIGUOUS"
    UNMAPPED = "UNMAPPED"


_LEGACY_RECORD_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class LegacyRecord:
    raw_json_text: str
    parsed_payload: Any

    def __init__(self, raw_json_text: str, parsed_payload: Any, *, _factory_token=None):
        if _factory_token is not _LEGACY_RECORD_FACTORY_TOKEN:
            raise ValueError("legacy records are issued only by the lossless reader")
        object.__setattr__(self, "raw_json_text", raw_json_text)
        object.__setattr__(self, "parsed_payload", parsed_payload)

    @classmethod
    def read(cls, raw_json_text: str) -> "LegacyRecord":
        if not isinstance(raw_json_text, str):
            raise TypeError("legacy JSON input must be text")
        return cls(
            raw_json_text,
            json.loads(raw_json_text),
            _factory_token=_LEGACY_RECORD_FACTORY_TOKEN,
        )

_LEGACY_BYTE_ENVELOPE_TOKEN = object()


@dataclass(frozen=True)
class LegacyCompatibilityProjection:
    raw_reason_id: Optional[str]
    mapped_reason_id: Optional[str]
    mapping_certainty: LegacyMappingCertainty
    raw_payload: Any
    non_authoritative: bool = True

    def __post_init__(self) -> None:
        if not self.non_authoritative:
            raise ValueError("legacy compatibility projections are never authoritative")


_LEGACY_MAPPING_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class SealedLegacyMappingRegistry:
    _mappings: Mapping[str, tuple[Optional[str], LegacyMappingCertainty]]

    def __init__(self, mappings, *, _factory_token=None):
        if _factory_token is not _LEGACY_MAPPING_FACTORY_TOKEN:
            raise ValueError("sealed legacy mapping registries are factory-issued")
        object.__setattr__(self, "_mappings", MappingProxyType(dict(mappings)))

    @classmethod
    def build(
        cls,
        entries: Iterable[
            tuple[str, Optional[str], LegacyMappingCertainty]
        ],
    ) -> "SealedLegacyMappingRegistry":
        copied: dict[str, tuple[Optional[str], LegacyMappingCertainty]] = {}
        for raw_id, mapped_id, certainty in entries:
            if not raw_id or raw_id in copied:
                raise ValueError("invalid/duplicate legacy mapping key")
            copied[raw_id] = (mapped_id, LegacyMappingCertainty(certainty))
        return cls(
            dict(sorted(copied.items())),
            _factory_token=_LEGACY_MAPPING_FACTORY_TOKEN,
        )

    def project(self, record: LegacyRecord) -> LegacyCompatibilityProjection:
        payload = record.parsed_payload
        raw_reason = payload.get("reason_id") if isinstance(payload, Mapping) else None
        raw_reason = str(raw_reason) if raw_reason is not None else None
        mapped, certainty = self._mappings.get(
            raw_reason, (None, LegacyMappingCertainty.UNMAPPED)
        )
        return LegacyCompatibilityProjection(raw_reason, mapped, certainty, payload)
