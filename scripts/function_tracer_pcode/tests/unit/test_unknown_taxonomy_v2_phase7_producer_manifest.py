import copy
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.v2.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
)
from scripts.function_tracer_pcode.validation.phase7_producer_manifest import (
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
