import copy
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.domains.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
)
from scripts.function_tracer_pcode.reporting.phase7_producer_manifest import (
    build_phase7_producer_manifest,
    validate_phase7_producer_manifest,
)


def test_phase7_producer_manifest_rejects_drift():
    root = Path(__file__).resolve().parents[4]
    payload = build_phase7_producer_manifest(root)
    tampered = copy.deepcopy(payload)
    tampered["sites"][0]["source_sha256"] = "0" * 64
    with pytest.raises(ValueError, match="drifted"):
        validate_phase7_producer_manifest(root, tampered)


def test_tracked_phase7_producer_manifest_matches_the_source_tree():
    """The tracked artifact must be regenerated whenever a pinned producer
    site moves (line) or its file changes (sha256):

        python3 -B -m scripts.function_tracer_pcode.reporting.phase7_producer_manifest \\
            --output artifacts/unknown_taxonomy_v2/phase7/producer-sites.json
    """
    root = Path(__file__).resolve().parents[4]
    tracked = json.loads(
        (root / "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json").read_text(encoding="utf-8")
    )
    validate_phase7_producer_manifest(root, tracked)
