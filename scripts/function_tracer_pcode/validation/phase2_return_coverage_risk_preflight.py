"""Select Phase 2 producer preflight pairs from return-coverage risk logs."""

from __future__ import annotations

import argparse
import ast
import shlex
import subprocess
from pathlib import Path
from typing import Dict, Iterable, Optional, Sequence, Tuple

from .result_summary import STATUS_EQ, STATUS_UNKNOWN, parse_log_identity


RISK_NOTES = (
    "call_wrapper_return_recovery",
    "control_region_return_recovery",
    "counted_scalar_loop_summary",
    "pre_return_counted_loop_summary",
    "state_transition_loop_summary",
    "switch_return_recovery",
)
PAIR_LABEL_SEPARATOR = " \N{LEFT RIGHT ARROW} "

DEFAULT_FALLBACK_PAIRS = (
    "fc_recursive_sum:B3_B7",
    "fc_dispatch_indirect:B1_B2",
    "fc_dispatch_indirect:B3_B4",
)


def select_risk_pairs(
    current_log_root: Path,
    *,
    baseline_log_root: Optional[Path] = None,
    max_per_stratum: int = 2,
    max_evidence_only_per_stratum: int = 1,
    fallback_pairs: Sequence[str] = DEFAULT_FALLBACK_PAIRS,
) -> Tuple[str, ...]:
    baseline_eq = (
        _eq_pair_filter_entries(baseline_log_root)
        if baseline_log_root is not None and baseline_log_root.is_dir()
        else None
    )
    strata: Dict[Tuple[str, Tuple[str, ...]], list] = {}
    for function_name, entry, status, notes, has_completed_evidence in _risk_log_infos(current_log_root):
        if status != STATUS_EQ:
            continue
        if not notes and not has_completed_evidence:
            continue
        if baseline_eq is not None and entry not in baseline_eq:
            continue
        strata.setdefault((function_name, notes), []).append(entry)

    selected = []
    seen = set()
    for (_function_name, notes), entries in sorted(strata.items()):
        limit = (
            max(1, int(max_per_stratum))
            if notes
            else max(0, int(max_evidence_only_per_stratum))
        )
        for entry in entries[:limit]:
            if entry in seen:
                continue
            selected.append(entry)
            seen.add(entry)

    for entry in fallback_pairs:
        if entry not in seen:
            selected.append(entry)
            seen.add(entry)
    return tuple(selected)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emit shell exports for risk-stratified Phase 2 producer preflight pairs."
    )
    parser.add_argument("--current-log-root", required=True)
    parser.add_argument("--baseline-log-root", default=None)
    parser.add_argument("--max-per-stratum", type=int, default=2)
    parser.add_argument("--max-evidence-only-per-stratum", type=int, default=1)
    parser.add_argument(
        "--fallback-pair",
        action="append",
        default=None,
        help="function:B1_B2 fallback; may be repeated",
    )
    args = parser.parse_args(argv)

    selected = select_risk_pairs(
        Path(args.current_log_root),
        baseline_log_root=Path(args.baseline_log_root) if args.baseline_log_root else None,
        max_per_stratum=args.max_per_stratum,
        max_evidence_only_per_stratum=args.max_evidence_only_per_stratum,
        fallback_pairs=tuple(args.fallback_pair or DEFAULT_FALLBACK_PAIRS),
    )
    target_set = ",".join(dict.fromkeys(entry.split(":", 1)[0] for entry in selected))
    pair_filter = ",".join(selected)
    print(f"export FUNCTION_CALL_TARGET_SET={shlex.quote(target_set)}")
    print(f"export FUNCTION_CALL_PAIR_FILTER={shlex.quote(pair_filter)}")
    return 0


def _iter_pair_logs(root: Path) -> Iterable[Path]:
    if not root.is_dir():
        return ()
    return root.glob("*/*.log")


def _risk_log_infos(root: Path) -> Tuple[Tuple[str, str, str, Tuple[str, ...], bool], ...]:
    if not root.is_dir():
        return ()
    pattern = "|".join(
        ("^Result: EQUIVALENT", "^Result: UNKNOWN", "completed_recovery_proof_evidence")
        + tuple(RISK_NOTES)
    )
    try:
        result = subprocess.run(
            ["rg", "--no-ignore", "-n", "--glob", "*.log", pattern, str(root)],
            check=False,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError:
        return tuple(_quick_log_info(log_path) for log_path in sorted(_iter_pair_logs(root)))
    if result.returncode not in (0, 1):
        return tuple(_quick_log_info(log_path) for log_path in sorted(_iter_pair_logs(root)))
    records: Dict[Path, list] = {}
    for line in result.stdout.splitlines():
        parsed = _parse_ripgrep_line(line)
        if parsed is None:
            continue
        log_path, text = parsed
        record = records.setdefault(log_path, [STATUS_UNKNOWN, [], False])
        if text.startswith("Result: EQUIVALENT"):
            record[0] = STATUS_EQ
        elif text.startswith("Result: UNKNOWN"):
            record[0] = STATUS_UNKNOWN
        elif "completed_recovery_proof_evidence" in text:
            record[2] = True
        elif "Analysis notes:" in text:
            for note in _risk_notes_from_line(text):
                if note not in record[1]:
                    record[1].append(note)

    return tuple(
        (
            _entry_info_from_log_path(log_path)[0],
            _entry_info_from_log_path(log_path)[1],
            status,
            tuple(notes),
            bool(has_completed_evidence),
        )
        for log_path, (status, notes, has_completed_evidence) in sorted(records.items())
    )


def _eq_pair_filter_entries(root: Path) -> set:
    if not root.is_dir():
        return set()
    try:
        result = subprocess.run(
            ["rg", "--no-ignore", "-l", "--glob", "*.log", "^Result: EQUIVALENT", str(root)],
            check=False,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError:
        return {
            _quick_log_info(log_path)[1]
            for log_path in sorted(_iter_pair_logs(root))
            if _quick_log_info(log_path)[2] == STATUS_EQ
        }
    if result.returncode not in (0, 1):
        return {
            _quick_log_info(log_path)[1]
            for log_path in sorted(_iter_pair_logs(root))
            if _quick_log_info(log_path)[2] == STATUS_EQ
        }
    return {
        _entry_info_from_log_path(Path(line))[1]
        for line in result.stdout.splitlines()
        if line.endswith(".log")
    }


def _parse_ripgrep_line(line: str) -> Optional[Tuple[Path, str]]:
    parts = line.split(":", 2)
    if len(parts) != 3:
        return None
    path_text, _line_number, text = parts
    if not path_text.endswith(".log"):
        return None
    return Path(path_text), text


def _entry_info_from_log_path(log_path: Path) -> Tuple[str, str]:
    function_name, pair_id = parse_log_identity(log_path)
    return function_name, f"{function_name}:{pair_id.replace(PAIR_LABEL_SEPARATOR, '_')}"


def _risk_notes_from_line(line: str) -> Tuple[str, ...]:
    if "Analysis notes:" not in line:
        return ()
    _prefix, raw_notes = line.split("Analysis notes:", 1)
    try:
        parsed = ast.literal_eval(raw_notes.strip())
    except (SyntaxError, ValueError):
        return ()
    if not isinstance(parsed, (list, tuple)):
        return ()
    notes = []
    for note in parsed:
        note_text = str(note)
        if note_text in RISK_NOTES and note_text not in notes:
            notes.append(note_text)
    return tuple(notes)


def _quick_log_info(log_path: Path) -> Tuple[str, str, str, Tuple[str, ...], bool]:
    function_name, entry = _entry_info_from_log_path(log_path)
    status = STATUS_UNKNOWN
    notes = []
    has_completed_evidence = False
    with log_path.open(errors="replace") as handle:
        for line in handle:
            if line.startswith("Result: EQUIVALENT"):
                status = STATUS_EQ
            elif line.startswith("Result: UNKNOWN"):
                status = STATUS_UNKNOWN
            elif "completed_recovery_proof_evidence" in line:
                has_completed_evidence = True
            elif "Analysis notes:" in line:
                for note in _risk_notes_from_line(line):
                    if note not in notes:
                        notes.append(note)
    return function_name, entry, status, tuple(notes), has_completed_evidence


if __name__ == "__main__":
    raise SystemExit(main())
