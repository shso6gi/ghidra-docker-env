#!/usr/bin/env python3
"""Function-level source diff manifest over an EqBench benchmark tree (Issue #104).

The runner benchmark gate must not treat every ``EQUIVALENT`` in a ``Neq``
sample as a violation: a Neq *program* pair differs in some function, but the
unchanged helpers of that program are legitimately equivalent.  This manifest
records, mechanically and only from the actual C sources the runner compiles,
what is known about each function of each sample:

``source_relation``
    ``SOURCE_IDENTICAL`` / ``SOURCE_CHANGED`` / ``ADDED`` / ``REMOVED`` /
    ``PARSE_UNKNOWN`` -- the textual relation of the function definition
    between the two sides (comments and whitespace ignored).
``source_impact``
    ``DIRECTLY_CHANGED`` / ``CALLS_CHANGED_CALLEE`` /
    ``REFERENCES_CHANGED_GLOBAL`` / ``SIGNATURE_OR_TYPE_CONTEXT_CHANGED`` /
    ``NO_KNOWN_SOURCE_IMPACT`` / ``IMPACT_UNKNOWN`` -- whether the source
    change can reach the function's behaviour (direct edit, transitive call
    of an impacted function, reference to an identifier that appears in
    changed file-scope text, or an unattributable file-scope change).
``semantic_ground_truth``
    ``CONFIRMED_EQ`` / ``CONFIRMED_NOT_EQ`` / ``UNKNOWN``.  This is *never*
    derived from ``source_relation``: a source change is not a proof of
    semantic non-equivalence.  ``Eq`` samples are ``CONFIRMED_EQ`` by
    construction (one source file compiled on both sides).  ``Neq`` functions
    are ``UNKNOWN`` unless an explicit, reviewed annotation file
    (``--ground-truth``, TSV ``sample function verdict evidence``) says
    otherwise.

``C-Desc.json`` is read only for a discrepancy audit (``c_desc`` section):
it is benchmark metadata, can be wrong, and is never used to classify.
The checker never sees this manifest; it is an evaluation oracle only.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
import sys
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from list_c_functions import (
    FunctionDefinition,
    _mask_comments_and_literals,
    _matching_brace,
    _matching_paren,
    _skip_ws_and_attributes,
    _top_level_depths,
    iter_function_definitions,
)
from select_neq_functions import _normalized_definition, _remove_comments

MANIFEST_SCHEMA = "eqbench-function-diff-manifest-v1"
DEFAULT_GROUND_TRUTH_FILE = Path(__file__).resolve().parent / "neq_ground_truth.tsv"

LANE_EQ = "Eq"
LANE_NEQ = "Neq"

RELATION_IDENTICAL = "SOURCE_IDENTICAL"
RELATION_CHANGED = "SOURCE_CHANGED"
RELATION_ADDED = "ADDED"
RELATION_REMOVED = "REMOVED"
RELATION_PARSE_UNKNOWN = "PARSE_UNKNOWN"
SOURCE_RELATIONS = (
    RELATION_IDENTICAL, RELATION_CHANGED, RELATION_ADDED, RELATION_REMOVED, RELATION_PARSE_UNKNOWN,
)

IMPACT_DIRECT = "DIRECTLY_CHANGED"
IMPACT_CALLS = "CALLS_CHANGED_CALLEE"
IMPACT_GLOBAL = "REFERENCES_CHANGED_GLOBAL"
IMPACT_SIGNATURE = "SIGNATURE_OR_TYPE_CONTEXT_CHANGED"
IMPACT_NONE = "NO_KNOWN_SOURCE_IMPACT"
IMPACT_UNKNOWN = "IMPACT_UNKNOWN"
SOURCE_IMPACTS = (
    IMPACT_DIRECT, IMPACT_CALLS, IMPACT_GLOBAL, IMPACT_SIGNATURE, IMPACT_NONE, IMPACT_UNKNOWN,
)
# Impacts that mean "the source change may reach this function".
IMPACTED = frozenset({IMPACT_DIRECT, IMPACT_CALLS, IMPACT_GLOBAL, IMPACT_SIGNATURE, IMPACT_UNKNOWN})

TRUTH_EQ = "CONFIRMED_EQ"
TRUTH_NOT_EQ = "CONFIRMED_NOT_EQ"
TRUTH_UNKNOWN = "UNKNOWN"
GROUND_TRUTHS = (TRUTH_EQ, TRUTH_NOT_EQ, TRUTH_UNKNOWN)

EVIDENCE_EQ_SAME_SOURCE = "eq_sample_single_source"

C_DESC_FILE = "C-Desc.json"
C_DESC_MATCH_UNIQUE = "matches_unique_changed_function"
C_DESC_ONE_OF_MULTIPLE = "names_one_of_multiple_changed_functions"
C_DESC_SOURCE_IDENTICAL = "named_function_is_source_identical"
C_DESC_FUNCTION_NOT_FOUND = "named_function_not_in_source"
C_DESC_FUNCTION_NAME_MISSING = "function_name_field_missing"
C_DESC_FILE_MISSING = "c_desc_missing"
C_DESC_UNREADABLE = "c_desc_unreadable"
C_DESC_NOT_APPLICABLE = "not_applicable"

_IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
_CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
_C_KEYWORDS = frozenset(
    """auto break case char const continue default do double else enum extern float for goto if
    inline int long register restrict return short signed sizeof static struct switch typedef union
    unsigned void volatile while _Bool _Complex _Imaginary include define ifdef ifndef endif undef
    pragma elif error line NULL""".split()
)


# ---------------------------------------------------------------------------
# Source parsing
# ---------------------------------------------------------------------------


@dataclass
class ParsedSource:
    path: Path
    text: str
    definitions: Dict[str, FunctionDefinition]
    order: List[str]
    sha256: str

    @property
    def masked(self) -> str:
        return _mask_comments_and_literals(self.text)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _trim_declaration_start(text: str, definition: FunctionDefinition) -> FunctionDefinition:
    """``list_c_functions`` starts a declaration after the previous ``;``/``{``/``}``,
    so preprocessor lines before the first function would be read as part of
    its definition.  Drop leading blank / ``#`` lines: they are file-scope
    context and are attributed by identifier instead."""
    start = definition.declaration_start
    while start < definition.body_start:
        newline = text.find("\n", start, definition.body_start)
        line = text[start : newline if newline >= 0 else definition.body_start]
        if line.strip() and not line.lstrip().startswith("#"):
            break
        if newline < 0:
            break
        start = newline + 1
    if start == definition.declaration_start:
        return definition
    return FunctionDefinition(
        name=definition.name, declaration_start=start,
        body_start=definition.body_start, body_end=definition.body_end,
    )


def parse_source(path: Path) -> ParsedSource:
    text = path.read_text(encoding="utf-8", errors="ignore")
    definitions = [_trim_declaration_start(text, d) for d in iter_function_definitions(text)]
    if not definitions:
        raise ValueError(f"no non-main function definitions found: {path}")
    names = [definition.name for definition in definitions]
    if len(names) != len(set(names)):
        raise ValueError(f"duplicate function definitions found: {path}")
    return ParsedSource(
        path=path,
        text=text,
        definitions={definition.name: definition for definition in definitions},
        order=names,
        sha256=_sha256(path),
    )


_MAIN_RE = re.compile(r"\bmain\s*\(")


def _main_spans(text: str) -> List[Tuple[int, int]]:
    """Spans of ``main`` definitions (``list_c_functions`` skips them by name);
    they are program-driver code, not file-scope context."""
    masked = _mask_comments_and_literals(text)
    depths = _top_level_depths(masked)
    spans: List[Tuple[int, int]] = []
    for match in _MAIN_RE.finditer(masked):
        paren = match.end() - 1
        if depths[paren] != 0:
            continue
        close = _matching_paren(masked, paren)
        if close is None:
            continue
        body = _skip_ws_and_attributes(masked, close + 1)
        if body >= len(masked) or masked[body] != "{":
            continue
        end = _matching_brace(masked, body)
        if end is None:
            continue
        prefix = masked[: match.start()]
        start = max(prefix.rfind(";"), prefix.rfind("{"), prefix.rfind("}")) + 1
        spans.append((start, end))
    return spans


def _top_level_text(parsed: ParsedSource) -> str:
    """Source text outside every function definition (``main`` included), comments removed."""
    spans = [
        (parsed.definitions[name].declaration_start, parsed.definitions[name].body_end)
        for name in parsed.order
    ] + _main_spans(parsed.text)
    pieces: List[str] = []
    cursor = 0
    for start, end in sorted(spans):
        if start < cursor:
            continue
        pieces.append(parsed.text[cursor:start])
        cursor = end + 1
    pieces.append(parsed.text[cursor:])
    return _remove_comments("".join(pieces))


def _context_units(text: str) -> List[str]:
    """Split file-scope text into comparable units: one per preprocessor
    directive line, otherwise one per ``;``-terminated declaration (so a
    multi-line initializer is one unit and its identifiers stay attached)."""
    units: List[str] = []
    buffer: List[str] = []

    def flush() -> None:
        joined = " ".join(" ".join(part.split()) for part in buffer if part.strip())
        if joined:
            units.append(joined)
        buffer.clear()

    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            flush()
            units.append(" ".join(stripped.split()))
            continue
        buffer.append(stripped)
        if stripped.endswith(";") or stripped.endswith("}"):
            flush()
    flush()
    return units


@dataclass(frozen=True)
class ContextDiff:
    changed: bool
    identifiers: List[str]
    unattributable: bool  # a changed unit no identifier can attribute to a function


def changed_top_level_context(new: ParsedSource, old: ParsedSource) -> ContextDiff:
    """Diff the file-scope units and collect the identifiers on changed units.

    ``#include`` changes are ignored; ``#define`` / declarations contribute
    their identifiers; any other changed directive (``#pragma``, ``#if``...)
    or a changed unit without identifiers is *unattributable* and makes the
    otherwise unaffected functions ``IMPACT_UNKNOWN``."""
    new_units = _context_units(_top_level_text(new))
    old_units = _context_units(_top_level_text(old))
    if new_units == old_units:
        return ContextDiff(False, [], False)
    identifiers: set[str] = set()
    unattributable = False
    for line in difflib.unified_diff(old_units, new_units, lineterm="", n=0):
        if line.startswith(("---", "+++", "@@")) or line[:1] not in "+-":
            continue
        unit = line[1:].strip()
        if unit.startswith("#"):
            directive = unit[1:].split(None, 1)[0] if len(unit) > 1 else ""
            if directive == "include":
                continue
            if directive != "define":
                unattributable = True
                continue
        found = {
            match.group(0)
            for match in _IDENT_RE.finditer(_mask_comments_and_literals(unit))
            if match.group(0) not in _C_KEYWORDS
        }
        if found:
            identifiers.update(found)
        else:
            unattributable = True
    return ContextDiff(True, sorted(identifiers), unattributable)


def _identifiers_in(text: str) -> set[str]:
    return {m.group(0) for m in _IDENT_RE.finditer(_mask_comments_and_literals(text))}


def _calls(parsed: ParsedSource, name: str) -> set[str]:
    definition = parsed.definitions[name]
    body = parsed.text[definition.body_start : definition.body_end + 1]
    return {
        match.group(1)
        for match in _CALL_RE.finditer(_mask_comments_and_literals(body))
        if match.group(1) in parsed.definitions and match.group(1) != name
    }


# ---------------------------------------------------------------------------
# Function classification
# ---------------------------------------------------------------------------


@dataclass
class FunctionEntry:
    source_relation: str
    source_impact: str
    impact_details: List[str] = field(default_factory=list)
    semantic_ground_truth: str = TRUTH_UNKNOWN
    ground_truth_evidence: Optional[str] = None

    def as_dict(self) -> Dict[str, object]:
        return {
            "source_relation": self.source_relation,
            "source_impact": self.source_impact,
            "impact_details": list(self.impact_details),
            "semantic_ground_truth": self.semantic_ground_truth,
            "ground_truth_evidence": self.ground_truth_evidence,
        }


def classify_neq_functions(new: ParsedSource, old: ParsedSource) -> Tuple[Dict[str, FunctionEntry], bool, List[str]]:
    """Classify every function of a Neq source pair (no ground truth applied)."""
    names = list(new.order) + [name for name in old.order if name not in new.definitions]
    entries: Dict[str, FunctionEntry] = {}
    context = changed_top_level_context(new, old)
    context_changed, context_identifiers = context.changed, context.identifiers
    context_set = set(context_identifiers)

    for name in names:
        in_new = name in new.definitions
        in_old = name in old.definitions
        if in_new and not in_old:
            entries[name] = FunctionEntry(RELATION_ADDED, IMPACT_DIRECT, ["definition only in new source"])
        elif in_old and not in_new:
            entries[name] = FunctionEntry(RELATION_REMOVED, IMPACT_DIRECT, ["definition only in old source"])
        elif _normalized_definition(new.text, new.definitions[name]) != _normalized_definition(
            old.text, old.definitions[name]
        ):
            entries[name] = FunctionEntry(RELATION_CHANGED, IMPACT_DIRECT, ["definition text differs"])
        else:
            entries[name] = FunctionEntry(RELATION_IDENTICAL, IMPACT_NONE)

    # Identifier references to changed file-scope text (globals, macros,
    # typedefs, struct layouts...).  Signature references are separated from
    # body references so a layout/type change is distinguishable.
    for name, entry in entries.items():
        if entry.source_impact != IMPACT_NONE or not context_set:
            continue
        definition = new.definitions[name]
        signature = new.text[definition.declaration_start : definition.body_start]
        body = new.text[definition.body_start : definition.body_end + 1]
        signature_hits = sorted(_identifiers_in(signature) & context_set)
        body_hits = sorted(_identifiers_in(body) & context_set)
        if body_hits:
            entry.source_impact = IMPACT_GLOBAL
            entry.impact_details.append("body references changed file-scope identifiers: " + ", ".join(body_hits))
        if signature_hits:
            if entry.source_impact == IMPACT_NONE:
                entry.source_impact = IMPACT_SIGNATURE
            entry.impact_details.append(
                "signature references changed file-scope identifiers: " + ", ".join(signature_hits)
            )

    # Reverse call closure from every impacted function, over both sides.
    callers: Dict[str, set[str]] = defaultdict(set)
    for parsed in (new, old):
        for caller in parsed.order:
            for callee in _calls(parsed, caller):
                callers[callee].add(caller)
    seeds = [name for name, entry in entries.items() if entry.source_impact != IMPACT_NONE]
    pending = deque(seeds)
    reached: Dict[str, str] = {}
    while pending:
        callee = pending.popleft()
        for caller in callers[callee]:
            if caller in reached or entries[caller].source_impact != IMPACT_NONE:
                continue
            reached[caller] = callee
            pending.append(caller)
    for caller, callee in reached.items():
        entries[caller].source_impact = IMPACT_CALLS
        entries[caller].impact_details.append(f"calls impacted function {callee}")

    # A file-scope change that no identifier attributes to any function is
    # not evidence of "no impact": mark the remaining functions unknown.
    if context.unattributable:
        for entry in entries.values():
            if entry.source_impact == IMPACT_NONE:
                entry.source_impact = IMPACT_UNKNOWN
                entry.impact_details.append("file-scope text changed without attributable identifiers")

    return entries, context_changed, context_identifiers


# ---------------------------------------------------------------------------
# Ground-truth annotations
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class GroundTruthAnnotation:
    sample: str
    function: str
    verdict: str
    evidence: str


def load_ground_truth(path: Path) -> List[GroundTruthAnnotation]:
    annotations: List[GroundTruthAnnotation] = []
    seen: set[Tuple[str, str]] = set()
    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t")
        if line_no and [f.strip() for f in fields] == ["sample", "function", "verdict", "evidence"]:
            continue
        if len(fields) != 4:
            raise ValueError(f"{path}:{line_no}: expected 4 tab-separated fields, got {len(fields)}")
        sample, function, verdict, evidence = (value.strip() for value in fields)
        if verdict not in (TRUTH_EQ, TRUTH_NOT_EQ):
            raise ValueError(f"{path}:{line_no}: verdict must be {TRUTH_EQ} or {TRUTH_NOT_EQ}, got {verdict!r}")
        if not sample or not function or not evidence:
            raise ValueError(f"{path}:{line_no}: sample, function and evidence must be non-empty")
        if (sample, function) in seen:
            raise ValueError(f"{path}:{line_no}: duplicate annotation for {sample} {function}")
        seen.add((sample, function))
        annotations.append(GroundTruthAnnotation(sample, function, verdict, evidence))
    return annotations


# ---------------------------------------------------------------------------
# C-Desc audit (metadata quality only)
# ---------------------------------------------------------------------------


def audit_c_desc(sample_dir: Path, entries: Mapping[str, FunctionEntry]) -> Dict[str, object]:
    path = sample_dir / C_DESC_FILE
    if not path.is_file():
        return {"present": False, "function_name": None, "agreement": C_DESC_FILE_MISSING}
    try:
        payload = json.loads(path.read_text(encoding="utf-8", errors="ignore"))
    except ValueError:
        return {"present": True, "function_name": None, "agreement": C_DESC_UNREADABLE}
    name = payload.get("function name") if isinstance(payload, dict) else None
    if not isinstance(name, str) or not name:
        return {"present": True, "function_name": None, "agreement": C_DESC_FUNCTION_NAME_MISSING}
    changed = sorted(n for n, e in entries.items() if e.source_relation != RELATION_IDENTICAL)
    if name not in entries:
        agreement = C_DESC_FUNCTION_NOT_FOUND
    elif name in changed:
        agreement = C_DESC_MATCH_UNIQUE if len(changed) == 1 else C_DESC_ONE_OF_MULTIPLE
    else:
        agreement = C_DESC_SOURCE_IDENTICAL
    return {
        "present": True,
        "function_name": name,
        "agreement": agreement,
        "source_changed_functions": changed,
    }


# ---------------------------------------------------------------------------
# Benchmark tree walk
# ---------------------------------------------------------------------------


def _relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def iter_eq_samples(root: Path) -> Iterable[Tuple[str, Path, Path]]:
    """Yield (sample_identity, sample_dir, source) like the Eq runner does."""
    for eq_dir in sorted(p for p in root.rglob("Eq") if p.is_dir()):
        for base in ("newV", "new"):
            source = eq_dir / f"{base}.c"
            if source.is_file():
                yield f"{_relative(eq_dir, root)}/{base}", eq_dir, source


def iter_neq_samples(root: Path) -> Iterable[Tuple[str, Path, Path, Path]]:
    """Yield (sample_identity, sample_dir, new, old) like the Neq runner does."""
    for neq_dir in sorted(p for p in root.rglob("Neq") if p.is_dir()):
        for new, old in (("newV", "oldV"), ("new", "old")):
            new_path, old_path = neq_dir / f"{new}.c", neq_dir / f"{old}.c"
            if new_path.is_file() and old_path.is_file():
                yield f"{_relative(neq_dir, root)}/{new}-{old}", neq_dir, new_path, old_path
                break


def build_eq_sample(sample_dir: Path, source: Path) -> Dict[str, object]:
    record: Dict[str, object] = {
        "lane": LANE_EQ,
        "sources": {"new": str(source), "old": None},
        "source_sha256": {"new": _sha256(source), "old": None},
        "parse_status": "ok",
        "parse_error": None,
        "top_level_context_changed": False,
        "changed_context_identifiers": [],
        "c_desc": {"present": (sample_dir / C_DESC_FILE).is_file(), "function_name": None,
                   "agreement": C_DESC_NOT_APPLICABLE},
        "functions": {},
    }
    try:
        parsed = parse_source(source)
    except (OSError, ValueError) as exc:
        record["parse_status"] = "failed"
        record["parse_error"] = str(exc)
        return record
    record["functions"] = {
        name: FunctionEntry(
            RELATION_IDENTICAL, IMPACT_NONE, [],
            semantic_ground_truth=TRUTH_EQ, ground_truth_evidence=EVIDENCE_EQ_SAME_SOURCE,
        ).as_dict()
        for name in parsed.order
    }
    return record


def build_neq_sample(
    sample: str, sample_dir: Path, new: Path, old: Path,
    annotations: Mapping[Tuple[str, str], GroundTruthAnnotation],
) -> Dict[str, object]:
    record: Dict[str, object] = {
        "lane": LANE_NEQ,
        "sources": {"new": str(new), "old": str(old)},
        "source_sha256": {"new": _sha256(new), "old": _sha256(old)},
        "parse_status": "ok",
        "parse_error": None,
        "top_level_context_changed": None,
        "changed_context_identifiers": [],
        "c_desc": {"present": (sample_dir / C_DESC_FILE).is_file(), "function_name": None,
                   "agreement": C_DESC_NOT_APPLICABLE},
        "functions": {},
    }
    try:
        parsed_new, parsed_old = parse_source(new), parse_source(old)
    except (OSError, ValueError) as exc:
        record["parse_status"] = "failed"
        record["parse_error"] = str(exc)
        return record
    entries, context_changed, identifiers = classify_neq_functions(parsed_new, parsed_old)
    for name, entry in entries.items():
        annotation = annotations.get((sample, name))
        if annotation is not None:
            entry.semantic_ground_truth = annotation.verdict
            entry.ground_truth_evidence = annotation.evidence
    record["top_level_context_changed"] = context_changed
    record["changed_context_identifiers"] = identifiers
    record["c_desc"] = audit_c_desc(sample_dir, entries)
    record["functions"] = {name: entry.as_dict() for name, entry in entries.items()}
    return record


def build_manifest(
    root: Path, *, ground_truth: Optional[Path] = None,
) -> Dict[str, object]:
    annotations: Dict[Tuple[str, str], GroundTruthAnnotation] = {}
    ground_truth_info: Dict[str, object] = {"path": None, "sha256": None, "entries": 0}
    if ground_truth is not None:
        for annotation in load_ground_truth(ground_truth):
            annotations[(annotation.sample, annotation.function)] = annotation
        ground_truth_info = {
            "path": str(ground_truth), "sha256": _sha256(ground_truth), "entries": len(annotations),
        }

    samples: Dict[str, Dict[str, object]] = {}
    for sample, sample_dir, source in iter_eq_samples(root):
        samples[sample] = build_eq_sample(sample_dir, source)
    for sample, sample_dir, new, old in iter_neq_samples(root):
        samples[sample] = build_neq_sample(sample, sample_dir, new, old, annotations)

    resolved = {
        (sample, name)
        for sample, record in samples.items()
        for name in record["functions"]  # type: ignore[union-attr]
    }
    unresolved = sorted(
        f"{key[0]}\t{key[1]}" for key in annotations if key not in resolved
    )
    counts = summarize(samples)
    return {
        "schema": MANIFEST_SCHEMA,
        "benchmark_root": str(root),
        "ground_truth": {**ground_truth_info, "unresolved_annotations": unresolved},
        "summary": counts,
        "samples": samples,
    }


def summarize(samples: Mapping[str, Mapping[str, object]]) -> Dict[str, object]:
    by_lane: Dict[str, Dict[str, int]] = {LANE_EQ: {}, LANE_NEQ: {}}
    parse_failed = 0
    c_desc: Dict[str, int] = {}
    for record in samples.values():
        lane = str(record["lane"])
        if record["parse_status"] != "ok":
            parse_failed += 1
        lane_counts = by_lane.setdefault(lane, {})
        lane_counts["samples"] = lane_counts.get("samples", 0) + 1
        for entry in record["functions"].values():  # type: ignore[union-attr]
            for key in ("source_relation", "source_impact", "semantic_ground_truth"):
                bucket = f"{key}:{entry[key]}"
                lane_counts[bucket] = lane_counts.get(bucket, 0) + 1
        if lane == LANE_NEQ:
            agreement = str(record["c_desc"]["agreement"])  # type: ignore[index]
            c_desc[agreement] = c_desc.get(agreement, 0) + 1
    return {"by_lane": by_lane, "parse_failed_samples": parse_failed, "c_desc_agreement": c_desc}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def format_summary(manifest: Mapping[str, object]) -> str:
    summary = manifest["summary"]
    lines = [f"function diff manifest: {len(manifest['samples'])} samples"]  # type: ignore[arg-type]
    for lane, counts in summary["by_lane"].items():  # type: ignore[index]
        lines.append(f"  {lane}: " + " ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    lines.append(f"  parse_failed_samples={summary['parse_failed_samples']}")  # type: ignore[index]
    lines.append("  c_desc_agreement: " + " ".join(
        f"{k}={v}" for k, v in sorted(summary["c_desc_agreement"].items())  # type: ignore[index]
    ))
    unresolved = manifest["ground_truth"]["unresolved_annotations"]  # type: ignore[index]
    lines.append(f"  ground_truth_entries={manifest['ground_truth']['entries']} unresolved={len(unresolved)}")  # type: ignore[index]
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--benchmark-root", type=Path, required=True,
                        help="EqBench benchmarks directory (EQBENCH_ROOT / NEQ_ROOT of the runners)")
    parser.add_argument("--output", type=Path, required=True, help="manifest JSON to write")
    parser.add_argument("--ground-truth", type=Path, default=None,
                        help="reviewed Neq ground-truth TSV (sample, function, verdict, evidence); "
                             f"default: {DEFAULT_GROUND_TRUTH_FILE} when it exists")
    parser.add_argument("--no-ground-truth", action="store_true", help="ignore the default annotation file")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    root = args.benchmark_root
    if not root.is_dir():
        print(f"error: benchmark root is not a directory: {root}", file=sys.stderr)
        return 2
    ground_truth = args.ground_truth
    if ground_truth is None and not args.no_ground_truth and DEFAULT_GROUND_TRUTH_FILE.is_file():
        ground_truth = DEFAULT_GROUND_TRUTH_FILE
    try:
        manifest = build_manifest(root, ground_truth=ground_truth)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(manifest, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(format_summary(manifest))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
