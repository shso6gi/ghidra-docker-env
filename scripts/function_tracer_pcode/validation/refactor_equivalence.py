"""Canonical behavior comparison for semantics-preserving refactors."""

from __future__ import annotations

import argparse
from collections.abc import Mapping, Sequence
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .result_summary import (
    ValidationLogRecord,
    canonical_validation_surface,
    read_validation_log_record,
)


SCHEMA_VERSION = 1
_VOLATILE_KEYS = frozenset(
    {
        "elapsed",
        "elapsed_seconds",
        "timestamp",
        "started_at",
        "finished_at",
        "temporary_path",
        "tmp_path",
    }
)
# Only a CPython-style object identity is volatile. Program addresses, P-code
# references, storage offsets, and call targets are semantic evidence.
_OBJECT_REPR_ADDRESS_RE = re.compile(r"(?<= object at )0x[0-9a-fA-F]+(?=>)")
_GENERATED_SYMBOL_RE = re.compile(
    r"^(?:(?:tmp|aux|unknown|fresh|phi|ret)_[0-9]+|rtunk_[0-9a-fA-F]+_[0-9]+)$"
)
_TOKEN_RE = re.compile(
    r'''\s*(?:(;[^\n]*(?:\n|$))|([()])|("(?:\\.|[^"\\])*")|([^\s()]+))'''
)


def _stable_json_value(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        if isinstance(value, str):
            return _OBJECT_REPR_ADDRESS_RE.sub("<object-address>", value)
        return value
    if isinstance(value, Mapping):
        return {
            str(key): _stable_json_value(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
            if str(key) not in _VOLATILE_KEYS
        }
    if isinstance(value, (set, frozenset)):
        normalized = [_stable_json_value(item) for item in value]
        return sorted(normalized, key=_json_sort_key)
    if isinstance(value, Sequence) and not isinstance(value, (bytes, bytearray)):
        if (
            (
                len(value) >= 3
                and value[0] == "function"
                and isinstance(value[1], int)
            )
            or (
                len(value) >= 4
                and value[0] == "parameter"
                and isinstance(value[1], int)
                and isinstance(value[2], int)
            )
        ):
            # Ghidra's ProgramDB-backed function id is allocated again whenever
            # the same binary is imported into a fresh temporary project.  It is
            # therefore process/project identity, not a program address.  Keep
            # the function entry and every remaining semantic key component.
            value = (value[0], "<program-object-id>", *value[2:])
        return [_stable_json_value(item) for item in value]
    return {
        "type": f"{type(value).__module__}.{type(value).__qualname__}",
        "repr": _OBJECT_REPR_ADDRESS_RE.sub("<object-address>", repr(value)),
    }


def _json_sort_key(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def canonical_json_hash(value: Any) -> str:
    payload = json.dumps(
        _stable_json_value(value), sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def tokenize_smt2(text: str) -> Tuple[str, ...]:
    tokens: List[str] = []
    position = 0
    while position < len(text):
        match = _TOKEN_RE.match(text, position)
        if match is None:
            if text[position:].strip():
                raise ValueError(f"invalid SMT-LIB near offset {position}")
            break
        position = match.end()
        comment, paren, quoted, atom = match.groups()
        if comment is not None:
            continue
        token = paren or quoted or atom
        if token is not None:
            tokens.append(token)
    return tuple(tokens)


def parse_smt2(text: str) -> Tuple[Any, ...]:
    tokens = tokenize_smt2(text)
    stack: List[List[Any]] = [[]]
    for token in tokens:
        if token == "(":
            child: List[Any] = []
            stack[-1].append(child)
            stack.append(child)
        elif token == ")":
            if len(stack) == 1:
                raise ValueError("unexpected closing parenthesis in SMT-LIB")
            stack.pop()
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ValueError("unterminated SMT-LIB expression")
    return tuple(stack[0])


def _as_tuple(value: Any) -> Any:
    if isinstance(value, list):
        return tuple(_as_tuple(item) for item in value)
    return value


def _command_name(command: Any) -> Optional[str]:
    if not isinstance(command, list) or not command:
        return None
    return str(command[0])


def _canonicalize_commutative_expression(value: Any) -> Any:
    if not isinstance(value, list):
        return value
    normalized = [_canonicalize_commutative_expression(item) for item in value]
    if (
        normalized
        and isinstance(normalized[0], str)
        and normalized[0] in {"and", "or", "=", "distinct", "+", "*"}
    ):
        head = normalized[0]
        tail = sorted(normalized[1:], key=lambda item: repr(_as_tuple(item)))
        return [head, *tail]
    return normalized


def _symbol_bindings(query_event: Mapping[str, Any]) -> Mapping[str, Any]:
    bindings = query_event.get("symbol_bindings")
    return bindings if isinstance(bindings, Mapping) else {}


def _alpha_symbol_map(tree: Sequence[Any], query_event: Mapping[str, Any]) -> Dict[str, str]:
    bindings = _symbol_bindings(query_event)
    mapping: Dict[str, str] = {}
    generated = []

    def visit(value: Any) -> None:
        if isinstance(value, list):
            for item in value:
                visit(item)
            return
        if not isinstance(value, str):
            return
        binding = bindings.get(value)
        if binding is not None:
            stable_binding = canonical_json_hash(binding)[:16]
            mapping[value] = f"generated@{stable_binding}"
        elif _GENERATED_SYMBOL_RE.match(value):
            generated.append(value)

    visit(list(tree))
    for index, symbol in enumerate(sorted(set(generated))):
        # Runtime-unknown names include process/program identity hashes. Their
        # equality relationships matter, while their generated spelling does not.
        mapping.setdefault(
            symbol,
            f"generated@ordinal:{index}" if symbol.startswith("rtunk_") else symbol,
        )
    return mapping


def _replace_symbols(value: Any, replacements: Mapping[str, str]) -> Any:
    if isinstance(value, list):
        return [_replace_symbols(item, replacements) for item in value]
    if isinstance(value, str):
        return replacements.get(value, value)
    return value


def canonical_smt_surface(
    smt_text: str,
    *,
    query_event: Optional[Mapping[str, Any]] = None,
) -> Dict[str, str]:
    event = query_event or {}
    raw_stable = "\n".join(
        line.rstrip() for line in str(smt_text).replace("\r\n", "\n").splitlines()
    ).strip()
    tree = list(parse_smt2(raw_stable))
    declarations = []
    assertions = []
    ordered = []
    for command in tree:
        name = _command_name(command)
        normalized = _canonicalize_commutative_expression(command)
        if name in {"declare-const", "declare-fun", "define-fun", "define-sort"}:
            declarations.append(normalized)
        elif name == "assert":
            assertions.append(normalized)
        else:
            ordered.append(normalized)
    structural = [
        *sorted(declarations, key=lambda item: repr(_as_tuple(item))),
        *sorted(assertions, key=lambda item: repr(_as_tuple(item))),
        *ordered,
    ]
    alpha = _replace_symbols(structural, _alpha_symbol_map(structural, event))
    return {
        "raw_stable_hash": hashlib.sha256(raw_stable.encode("utf-8")).hexdigest(),
        "structural_exact_hash": canonical_json_hash(structural),
        "controlled_alpha_hash": canonical_json_hash(alpha),
    }


def _reason_tuples(payload: Mapping[str, Any]) -> List[Any]:
    records = payload.get("unknown_reasons") or payload.get("reason_records") or ()
    if not isinstance(records, Sequence) or isinstance(records, (str, bytes)):
        return []
    result = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        result.append(
            [
                record.get("reason_id"),
                record.get("decision_effect"),
                record.get("reason_scope"),
                record.get("recovery_proof_kind"),
                record.get("stage"),
                record.get("pair_or_case"),
            ]
        )
    return sorted(result, key=_json_sort_key)


def _record_refactor_surface(record: ValidationLogRecord) -> Dict[str, Any]:
    payloads = [payload for payload in record.payloads if isinstance(payload, Mapping)]
    return {
        "function_name": record.function_name,
        "pair_identity": record.pair_label,
        "final_result": record.status,
        "payloads": [
            {
                "reason_tuples": _reason_tuples(payload),
                "completed_proof_evidence": _stable_json_value(
                    payload.get("completed_recovery_proof_evidence") or ()
                ),
                "active_blockers": _stable_json_value(
                    payload.get("active_blockers")
                    or payload.get("active_unsafety_reasons")
                    or ()
                ),
                "coverage_gaps": _stable_json_value(
                    payload.get("coverage_gaps")
                    or payload.get("active_coverage_gaps")
                    or ()
                ),
                "counterexample_decisive": payload.get("counterexample_decisive"),
                "counterexample_replay": _stable_json_value(
                    payload.get("counterexample_replay")
                ),
            }
            for payload in payloads
        ],
    }


def _query_surface(query_event: Mapping[str, Any]) -> Dict[str, Any]:
    query = str(query_event.get("query") or query_event.get("smt_formula") or "")
    smt_surface = canonical_smt_surface(query, query_event=query_event) if query else None
    return {
        "pair_id": query_event.get("pair_id"),
        "stage": query_event.get("stage"),
        "status": query_event.get("status"),
        "timeout_budget": query_event.get("timeout_budget"),
        "fallback": query_event.get("fallback"),
        "counterexample_decisive": query_event.get("counterexample_decisive"),
        "counterexample_replay": _stable_json_value(query_event.get("counterexample_replay")),
        "smt": (
            {"major_structure_hash": smt_surface["controlled_alpha_hash"]}
            if smt_surface is not None
            else None
        ),
    }


def canonical_refactor_surface(
    records: Iterable[ValidationLogRecord],
    *,
    query_events: Iterable[Mapping[str, Any]] = (),
) -> Dict[str, Any]:
    record_tuple = tuple(records)
    record_surfaces = sorted(
        (_record_refactor_surface(record) for record in record_tuple),
        key=lambda item: _json_sort_key([item["function_name"], item["pair_identity"]]),
    )
    return {
        "schema_version": SCHEMA_VERSION,
        "validation": canonical_validation_surface(record_tuple),
        "records": record_surfaces,
        # These are attempt-level final-SMT surfaces. They do not represent every
        # condition/value query issued inside the pairwise executor. Attempt order
        # is still semantically relevant for phase fallback behavior.
        "queries": [_query_surface(event) for event in query_events],
    }


def canonical_refactor_surface_hash(
    records: Iterable[ValidationLogRecord],
    *,
    query_events: Iterable[Mapping[str, Any]] = (),
) -> str:
    return canonical_json_hash(
        canonical_refactor_surface(records, query_events=query_events)
    )


def compare_refactor_surfaces(
    before: Mapping[str, Any], after: Mapping[str, Any]
) -> Tuple[str, ...]:
    if before == after:
        return ()
    failures = []
    for key in ("validation", "records", "queries"):
        if before.get(key) != after.get(key):
            failures.append(f"{key}_changed")
    if before.get("schema_version") != after.get("schema_version"):
        failures.append("schema_version_changed")
    return tuple(failures or ("surface_changed",))


def attempt_final_smt_events_from_records(
    records: Iterable[ValidationLogRecord],
) -> Tuple[Mapping[str, Any], ...]:
    """Recover one ordered final-SMT surface per debug-trace attempt.

    This intentionally captures only ``attempt.final_smt`` and the attempt's
    first-definitive solver status. It does not capture every condition/value
    query executed by the pairwise query executor.
    """
    events: List[Mapping[str, Any]] = []
    for record in records:
        for payload in record.payloads:
            trace = payload.get("debug_trace") if isinstance(payload, Mapping) else None
            attempts = trace.get("attempts") if isinstance(trace, Mapping) else None
            if not isinstance(attempts, Sequence) or isinstance(attempts, (str, bytes)):
                continue
            for attempt_index, attempt in enumerate(attempts):
                if not isinstance(attempt, Mapping):
                    continue
                solver_results = attempt.get("solver_results")
                first = (
                    solver_results.get("first_definitive")
                    if isinstance(solver_results, Mapping)
                    else None
                )
                events.append(
                    {
                        "pair_id": f"{record.function_name}:{record.pair_label}",
                        "stage": attempt.get("phase") or attempt.get("stage_path"),
                        "attempt_index": attempt.get("attempt_id", attempt_index),
                        "status": first.get("status") if isinstance(first, Mapping) else None,
                        "fallback": attempt.get("transition_reason"),
                        "counterexample_decisive": attempt.get("pairwise_decisive"),
                        "counterexample_replay": attempt.get("counterexample_replay"),
                        "query": attempt.get("final_smt") or "",
                    }
                )
    return tuple(events)


def query_events_from_records(
    records: Iterable[ValidationLogRecord],
) -> Tuple[Mapping[str, Any], ...]:
    """Compatibility alias for :func:`attempt_final_smt_events_from_records`."""
    return attempt_final_smt_events_from_records(records)


def capture_refactor_surface_from_logs(paths: Iterable[Path]) -> Dict[str, Any]:
    records = tuple(read_validation_log_record(path) for path in paths)
    return canonical_refactor_surface(
        records,
        query_events=attempt_final_smt_events_from_records(records),
    )


def _expand_log_paths(values: Sequence[str]) -> Tuple[Path, ...]:
    paths: List[Path] = []
    for value in values:
        candidate = Path(value)
        if candidate.is_dir():
            paths.extend(sorted(candidate.rglob("*.log")))
        elif candidate.is_file():
            paths.append(candidate)
    return tuple(dict.fromkeys(path.resolve() for path in paths))


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Capture or compare behavior-preserving refactor evidence."
    )
    parser.add_argument("logs", nargs="+", help="validation log files or directories")
    parser.add_argument("--output", type=Path, help="write the canonical surface JSON")
    parser.add_argument("--baseline", type=Path, help="compare against this surface JSON")
    args = parser.parse_args(argv)
    paths = _expand_log_paths(args.logs)
    if not paths:
        parser.error("no validation logs found")
    surface = capture_refactor_surface_from_logs(paths)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(surface, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    if args.baseline:
        baseline = json.loads(args.baseline.read_text(encoding="utf-8"))
        failures = compare_refactor_surfaces(baseline, surface)
        if failures:
            print("refactor surface mismatch: " + ", ".join(failures))
            return 1
    print(
        json.dumps(
            {
                "logs": len(paths),
                "attempt_final_smt_surfaces": len(surface["queries"]),
                "hash": canonical_json_hash(surface),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
