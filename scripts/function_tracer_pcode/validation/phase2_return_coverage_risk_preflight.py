"""Select Phase 2 producer preflight pairs from return-coverage risk logs."""

from __future__ import annotations

import argparse
import ast
import json
import random
import re
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

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
DEFAULT_MAX_SELECTED_PAIRS = 24
DEFAULT_SAMPLE_SEED = 0


@dataclass(frozen=True)
class RiskLogInfo:
    function_name: str
    entry: str
    status: str
    notes: Tuple[str, ...]
    has_completed_evidence: bool
    binary_pair_shape: str
    side_shape: str
    proof_stages: Tuple[str, ...]
    object_target_shapes: Tuple[str, ...]


@dataclass(frozen=True)
class SelectedRiskPair:
    entry: str
    function_name: str
    status: str
    selection_reason: str
    stratum_key: Tuple[str, ...]
    notes: Tuple[str, ...]
    has_completed_evidence: bool
    binary_pair_shape: str
    side_shape: str
    proof_stages: Tuple[str, ...]
    object_target_shapes: Tuple[str, ...]


def select_risk_pairs(
    current_log_root: Path,
    *,
    baseline_log_root: Optional[Path] = None,
    max_per_stratum: int = 2,
    max_evidence_only_per_stratum: int = 1,
    max_pairs: int = DEFAULT_MAX_SELECTED_PAIRS,
    sample_seed: int = DEFAULT_SAMPLE_SEED,
    fallback_pairs: Sequence[str] = DEFAULT_FALLBACK_PAIRS,
) -> Tuple[str, ...]:
    return tuple(
        selected.entry
        for selected in select_risk_pair_infos(
            current_log_root,
            baseline_log_root=baseline_log_root,
            max_per_stratum=max_per_stratum,
            max_evidence_only_per_stratum=max_evidence_only_per_stratum,
            max_pairs=max_pairs,
            sample_seed=sample_seed,
            fallback_pairs=fallback_pairs,
        )
    )


def select_risk_pair_infos(
    current_log_root: Path,
    *,
    baseline_log_root: Optional[Path] = None,
    max_per_stratum: int = 2,
    max_evidence_only_per_stratum: int = 1,
    max_pairs: int = DEFAULT_MAX_SELECTED_PAIRS,
    sample_seed: int = DEFAULT_SAMPLE_SEED,
    fallback_pairs: Sequence[str] = DEFAULT_FALLBACK_PAIRS,
) -> Tuple[SelectedRiskPair, ...]:
    baseline_eq = (
        _eq_pair_filter_entries(baseline_log_root)
        if baseline_log_root is not None and baseline_log_root.is_dir()
        else None
    )
    strata: Dict[Tuple[str, ...], list] = {}
    for info in _risk_log_infos(current_log_root):
        if info.status != STATUS_EQ:
            continue
        if not info.notes and not info.has_completed_evidence:
            continue
        if baseline_eq is not None and info.entry not in baseline_eq:
            continue
        strata.setdefault(_risk_stratum_key(info), []).append(info)

    candidates_by_function: Dict[str, list] = {}
    rng = random.Random(int(sample_seed))
    for stratum_key, entries in sorted(strata.items()):
        note_key = stratum_key[1]
        limit = (
            max(1, int(max_per_stratum))
            if note_key != "evidence-only"
            else max(0, int(max_evidence_only_per_stratum))
        )
        shuffled_entries = sorted(entries, key=lambda info: info.entry)
        rng.shuffle(shuffled_entries)
        for info in shuffled_entries[:limit]:
            candidates_by_function.setdefault(info.function_name, []).append(
                _selected_risk_pair(info, stratum_key, "risk-stratum")
            )

    selected = []
    seen = set()
    function_names = sorted(candidates_by_function)
    max_selected = max(0, int(max_pairs))
    fallback_reserve = len(tuple(fallback_pairs)) if max_selected > len(tuple(fallback_pairs)) else 0
    risk_limit = max(0, max_selected - fallback_reserve)
    function_names = _append_round_robin_candidates(
        selected,
        seen,
        candidates_by_function,
        function_names,
        risk_limit,
    )

    for entry in fallback_pairs:
        if len(selected) >= max_selected:
            break
        if entry in seen:
            continue
        function_name = entry.split(":", 1)[0]
        selected.append(
            SelectedRiskPair(
                entry=entry,
                function_name=function_name,
                status="fallback",
                selection_reason="fallback",
                stratum_key=("fallback", function_name),
                notes=(),
                has_completed_evidence=False,
                binary_pair_shape="unknown",
                side_shape="unknown",
                proof_stages=(),
                object_target_shapes=(),
            )
        )
        seen.add(entry)

    _append_round_robin_candidates(
        selected,
        seen,
        candidates_by_function,
        function_names,
        max_selected,
    )
    return tuple(selected)


def _append_round_robin_candidates(
    selected: list,
    seen: set,
    candidates_by_function: Dict[str, list],
    function_names: Sequence[str],
    limit: int,
) -> list:
    function_names = list(function_names)
    while len(selected) < limit and function_names:
        next_function_names = []
        for index, function_name in enumerate(function_names):
            entries = candidates_by_function[function_name]
            while entries:
                candidate = entries.pop(0)
                if candidate.entry in seen:
                    continue
                selected.append(candidate)
                seen.add(candidate.entry)
                break
            if entries:
                next_function_names.append(function_name)
            if len(selected) >= limit:
                next_function_names.extend(function_names[index + 1 :])
                break
        function_names = next_function_names
    return list(function_names)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emit shell exports for risk-stratified Phase 2 producer preflight pairs."
    )
    parser.add_argument("--current-log-root", required=True)
    parser.add_argument("--baseline-log-root", default=None)
    parser.add_argument("--max-per-stratum", type=int, default=2)
    parser.add_argument("--max-evidence-only-per-stratum", type=int, default=1)
    parser.add_argument("--max-pairs", type=int, default=DEFAULT_MAX_SELECTED_PAIRS)
    parser.add_argument("--sample-seed", type=int, default=DEFAULT_SAMPLE_SEED)
    parser.add_argument("--manifest-path", default=None)
    parser.add_argument(
        "--fallback-pair",
        action="append",
        default=None,
        help="function:B1_B2 fallback; may be repeated",
    )
    args = parser.parse_args(argv)

    selected_infos = select_risk_pair_infos(
        Path(args.current_log_root),
        baseline_log_root=Path(args.baseline_log_root) if args.baseline_log_root else None,
        max_per_stratum=args.max_per_stratum,
        max_evidence_only_per_stratum=args.max_evidence_only_per_stratum,
        max_pairs=args.max_pairs,
        sample_seed=args.sample_seed,
        fallback_pairs=tuple(args.fallback_pair or DEFAULT_FALLBACK_PAIRS),
    )
    selected = tuple(info.entry for info in selected_infos)
    _emit_selection_summary(selected_infos, args, stream=sys.stderr)
    if args.manifest_path:
        _write_selection_manifest(Path(args.manifest_path), selected_infos, args)
    target_set = ",".join(dict.fromkeys(entry.split(":", 1)[0] for entry in selected))
    pair_filter = ",".join(selected)
    print(f"export FUNCTION_CALL_TARGET_SET={shlex.quote(target_set)}")
    print(f"export FUNCTION_CALL_PAIR_FILTER={shlex.quote(pair_filter)}")
    print(f"export RISK_PREFLIGHT_SELECTED_COUNT={len(selected)}")
    return 0


def _iter_pair_logs(root: Path) -> Iterable[Path]:
    if not root.is_dir():
        return ()
    return root.glob("*/*.log")


def _risk_log_infos(root: Path) -> Tuple[RiskLogInfo, ...]:
    if not root.is_dir():
        return ()
    pattern = "|".join(
        (
            "^Result: EQUIVALENT",
            "^Result: UNKNOWN",
            "completed_recovery_proof_evidence",
            '"binary1_name"',
            '"binary2_name"',
        )
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
        record = records.setdefault(log_path, [STATUS_UNKNOWN, [], False, [], [], None])
        payload_facts = _payload_facts_from_line(text)
        if text.startswith("Result: EQUIVALENT"):
            record[0] = STATUS_EQ
        elif text.startswith("Result: UNKNOWN"):
            record[0] = STATUS_UNKNOWN
        if payload_facts.has_completed_evidence:
            record[2] = True
            _extend_unique(record[3], payload_facts.proof_stages)
            _extend_unique(record[4], payload_facts.object_target_shapes)
        elif "completed_recovery_proof_evidence" in text:
            record[2] = True
            _extend_unique(record[3], _proof_stages_from_line(text))
            _extend_unique(record[4], _object_target_shapes_from_line(text))
        if payload_facts.binary_names is not None:
            record[5] = payload_facts.binary_names
        elif '"binary1_name"' in text or '"binary2_name"' in text:
            record[5] = _payload_binary_names_from_line(text) or record[5]
        if "Analysis notes:" in text:
            for note in _risk_notes_from_line(text):
                if note not in record[1]:
                    record[1].append(note)

    return tuple(
        _risk_log_info_from_parts(
            log_path,
            status=status,
            notes=tuple(notes),
            has_completed_evidence=bool(has_completed_evidence),
            proof_stages=tuple(proof_stages),
            object_target_shapes=tuple(object_target_shapes),
            payload_binary_names=payload_binary_names,
        )
        for log_path, (
            status,
            notes,
            has_completed_evidence,
            proof_stages,
            object_target_shapes,
            payload_binary_names,
        ) in sorted(records.items())
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
            _quick_log_info(log_path).entry
            for log_path in sorted(_iter_pair_logs(root))
            if _quick_log_info(log_path).status == STATUS_EQ
        }
    if result.returncode not in (0, 1):
        return {
            _quick_log_info(log_path).entry
            for log_path in sorted(_iter_pair_logs(root))
            if _quick_log_info(log_path).status == STATUS_EQ
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


def _quick_log_info(log_path: Path) -> RiskLogInfo:
    function_name, entry = _entry_info_from_log_path(log_path)
    status = STATUS_UNKNOWN
    notes = []
    has_completed_evidence = False
    proof_stages = []
    object_target_shapes = []
    payload_binary_names = None
    with log_path.open(errors="replace") as handle:
        for line in handle:
            payload_facts = _payload_facts_from_line(line)
            if line.startswith("Result: EQUIVALENT"):
                status = STATUS_EQ
            elif line.startswith("Result: UNKNOWN"):
                status = STATUS_UNKNOWN
            if payload_facts.has_completed_evidence:
                has_completed_evidence = True
                _extend_unique(proof_stages, payload_facts.proof_stages)
                _extend_unique(object_target_shapes, payload_facts.object_target_shapes)
            elif "completed_recovery_proof_evidence" in line:
                has_completed_evidence = True
                _extend_unique(proof_stages, _proof_stages_from_line(line))
                _extend_unique(object_target_shapes, _object_target_shapes_from_line(line))
            if payload_facts.binary_names is not None:
                payload_binary_names = payload_facts.binary_names
            elif '"binary1_name"' in line or '"binary2_name"' in line:
                payload_binary_names = _payload_binary_names_from_line(line) or payload_binary_names
            if "Analysis notes:" in line:
                for note in _risk_notes_from_line(line):
                    if note not in notes:
                        notes.append(note)
    return _risk_log_info_from_parts(
        log_path,
        status=status,
        notes=tuple(notes),
        has_completed_evidence=has_completed_evidence,
        proof_stages=tuple(proof_stages),
        object_target_shapes=tuple(object_target_shapes),
        payload_binary_names=payload_binary_names,
        function_name=function_name,
        entry=entry,
    )


def _risk_log_info_from_parts(
    log_path: Path,
    *,
    status: str,
    notes: Tuple[str, ...],
    has_completed_evidence: bool,
    proof_stages: Tuple[str, ...],
    object_target_shapes: Tuple[str, ...],
    payload_binary_names: Optional[Tuple[str, str]] = None,
    function_name: Optional[str] = None,
    entry: Optional[str] = None,
) -> RiskLogInfo:
    parsed_function_name, parsed_entry = _entry_info_from_log_path(log_path)
    function_name = function_name or parsed_function_name
    entry = entry or parsed_entry
    left_binary, right_binary = payload_binary_names or _binary_names_from_entry(entry)
    left_shape = _binary_shape(left_binary)
    right_shape = _binary_shape(right_binary)
    normalized_proof_stages = tuple(sorted(proof_stages))
    normalized_object_target_shapes = tuple(sorted(object_target_shapes))
    if has_completed_evidence:
        normalized_proof_stages = normalized_proof_stages or ("unknown",)
        normalized_object_target_shapes = normalized_object_target_shapes or ("unknown",)
    return RiskLogInfo(
        function_name=function_name,
        entry=entry,
        status=status,
        notes=tuple(sorted(notes)),
        has_completed_evidence=has_completed_evidence,
        binary_pair_shape=" ↔ ".join(sorted((left_shape, right_shape))),
        side_shape=f"{left_shape} -> {right_shape}",
        proof_stages=normalized_proof_stages,
        object_target_shapes=normalized_object_target_shapes,
    )


def _risk_stratum_key(info: RiskLogInfo) -> Tuple[str, ...]:
    note_key = ",".join(info.notes) if info.notes else "evidence-only"
    proof_stage_key = ",".join(info.proof_stages) if info.proof_stages else "none"
    object_key = ",".join(info.object_target_shapes) if info.object_target_shapes else "none"
    return (
        info.function_name,
        note_key,
        info.binary_pair_shape,
        info.side_shape,
        proof_stage_key,
        object_key,
    )


def _selected_risk_pair(
    info: RiskLogInfo,
    stratum_key: Tuple[str, ...],
    selection_reason: str,
) -> SelectedRiskPair:
    return SelectedRiskPair(
        entry=info.entry,
        function_name=info.function_name,
        status=info.status,
        selection_reason=selection_reason,
        stratum_key=stratum_key,
        notes=info.notes,
        has_completed_evidence=info.has_completed_evidence,
        binary_pair_shape=info.binary_pair_shape,
        side_shape=info.side_shape,
        proof_stages=info.proof_stages,
        object_target_shapes=info.object_target_shapes,
    )


def _emit_selection_summary(
    selected_infos: Sequence[SelectedRiskPair],
    args: argparse.Namespace,
    *,
    stream,
) -> None:
    print("Phase 2 return coverage risk preflight selection:", file=stream)
    print(f"  selected pairs: {len(selected_infos)}", file=stream)
    print(f"  max pairs: {args.max_pairs}", file=stream)
    print(f"  sample seed: {args.sample_seed}", file=stream)
    for info in selected_infos:
        notes = ",".join(info.notes) if info.notes else "-"
        proof = ",".join(info.proof_stages) if info.proof_stages else "-"
        print(
            "  - "
            f"{info.entry} | reason={info.selection_reason} | "
            f"notes={notes} | side={info.side_shape} | proof_stage={proof}",
            file=stream,
        )


def _write_selection_manifest(
    manifest_path: Path,
    selected_infos: Sequence[SelectedRiskPair],
    args: argparse.Namespace,
) -> None:
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "current_log_root": args.current_log_root,
        "baseline_log_root": args.baseline_log_root,
        "max_per_stratum": args.max_per_stratum,
        "max_evidence_only_per_stratum": args.max_evidence_only_per_stratum,
        "max_pairs": args.max_pairs,
        "sample_seed": args.sample_seed,
        "selected_count": len(selected_infos),
        "selected_pairs": [asdict(info) for info in selected_infos],
    }
    manifest_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def _extend_unique(values: list, new_values: Iterable[str]) -> None:
    for value in new_values:
        if value not in values:
            values.append(value)


def _proof_stages_from_line(line: str) -> Tuple[str, ...]:
    return tuple(dict.fromkeys(re.findall(r'"proof_stage"\s*:\s*"([^"]+)"', line)))


def _object_target_shapes_from_line(line: str) -> Tuple[str, ...]:
    raw_keys = re.findall(r'"object_target_key"\s*:\s*"([^"]+)"', line)
    return tuple(dict.fromkeys(_object_target_shape(raw_key) for raw_key in raw_keys))


@dataclass(frozen=True)
class _PayloadFacts:
    binary_names: Optional[Tuple[str, str]]
    has_completed_evidence: bool
    proof_stages: Tuple[str, ...]
    object_target_shapes: Tuple[str, ...]


def _payload_facts_from_line(line: str) -> _PayloadFacts:
    payload = _json_payload_from_line(line)
    if payload is None:
        return _PayloadFacts(None, False, (), ())
    binary_names = _payload_binary_names(payload)
    evidence_records = _completed_recovery_proof_evidence(payload)
    proof_stages = []
    object_target_shapes = []
    for evidence_record in evidence_records:
        if not isinstance(evidence_record, Mapping):
            continue
        evidence = evidence_record.get("evidence")
        proof_stage = evidence_record.get("proof_stage")
        if proof_stage is None and isinstance(evidence, Mapping):
            proof_stage = evidence.get("proof_stage")
        if proof_stage is not None and str(proof_stage) not in proof_stages:
            proof_stages.append(str(proof_stage))
        object_target_key = None
        if isinstance(evidence, Mapping):
            object_target_key = evidence.get("object_target_key")
        if object_target_key is None:
            object_target_key = evidence_record.get("object_target_key")
        if object_target_key is not None:
            object_target_shape = _object_target_shape(object_target_key)
            if object_target_shape not in object_target_shapes:
                object_target_shapes.append(object_target_shape)
    return _PayloadFacts(
        binary_names=binary_names,
        has_completed_evidence=bool(evidence_records),
        proof_stages=tuple(proof_stages),
        object_target_shapes=tuple(object_target_shapes),
    )


def _json_payload_from_line(line: str) -> Optional[Mapping[str, Any]]:
    text = line.strip()
    if not text.startswith("{"):
        return None
    try:
        payload = json.loads(text)
    except json.JSONDecodeError:
        return None
    return payload if isinstance(payload, Mapping) else None


def _payload_binary_names(payload: Mapping[str, Any]) -> Optional[Tuple[str, str]]:
    left = payload.get("binary1_name")
    right = payload.get("binary2_name")
    if left is None or right is None:
        return None
    return str(left), str(right)


def _completed_recovery_proof_evidence(payload: Mapping[str, Any]) -> Tuple[Any, ...]:
    evidence = payload.get("completed_recovery_proof_evidence")
    if not isinstance(evidence, (list, tuple)):
        return ()
    return tuple(evidence)


def _object_target_shape(raw_key: Any) -> str:
    if isinstance(raw_key, str):
        text = raw_key
    else:
        text = json.dumps(raw_key, sort_keys=True, separators=(",", ":"))
    text = re.sub(r"0x[0-9a-fA-F]+", "0xADDR", text)
    text = re.sub(r"\b\d+\b", "N", text)
    return text[:120]


def _payload_binary_names_from_line(line: str) -> Optional[Tuple[str, str]]:
    payload = _json_payload_from_line(line)
    if payload is None:
        return None
    return _payload_binary_names(payload)


def _binary_names_from_entry(entry: str) -> Tuple[str, str]:
    pair_id = entry.split(":", 1)[1] if ":" in entry else entry
    if "_" in pair_id:
        left, right = pair_id.split("_", 1)
        return left, right
    return pair_id, pair_id


def _binary_shape(binary_name: str) -> str:
    name = Path(str(binary_name)).name
    if name.startswith("function_call_test-"):
        name = name[len("function_call_test-") :]
    parts = name.split("-")
    if len(parts) >= 3:
        arch, compiler, opt = parts[0], parts[1], parts[-1]
        return f"{arch}/{compiler}/{opt}"
    return name


if __name__ == "__main__":
    raise SystemExit(main())
