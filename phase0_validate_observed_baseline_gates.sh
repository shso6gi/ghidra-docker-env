#!/usr/bin/env bash
# Run all lightweight Phase 0 observed-baseline gates.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Phase 0 observed-baseline gates:"
echo "  - Phase 0A raw artifact integrity"
echo "  - Phase 0C observed-baseline census"
echo "  - Phase 0C canonical reproduction"
echo "  - Phase 0D NOT_EQ audit"

./phase0a_validate_observed_baseline_integrity_gate.sh
./phase0c_validate_observed_baseline_census_gate.sh
./phase0c_validate_canonical_reproduction_gate.sh
./phase0d_validate_not_eq_audit_gate.sh

echo ""
echo "Phase 0 observed-baseline gates finished."
