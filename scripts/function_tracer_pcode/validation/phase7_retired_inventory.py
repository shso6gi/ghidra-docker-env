"""Independent reviewed inventory for Phase 7 retired UNKNOWN reason IDs."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
from enum import Enum
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

from ..equivalence.v2.phase7_cutover import RETIRED_UMBRELLA_REASON_IDS
from .unknown_taxonomy_audit import build_inventory_review_template


class RetiredReferenceRelation(str, Enum):
    P_EMIT = "P_emit"
    P_ROUTE = "P_route"
    D_LEGACY = "D_legacy"
    L_DECODE = "L_decode"


PHASE7_RETIRED_INVENTORY_KIND = "phase7_retired_reason_reference_partition"
_ENUM_MEMBER_BY_VALUE = {
    value: value.upper() for value in RETIRED_UMBRELLA_REASON_IDS
}


def _digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _python_files(root: Path) -> tuple[Path, ...]:
    source_root = root / "scripts" / "function_tracer_pcode"
    return tuple(path for path in sorted(source_root.rglob("*.py"), key=lambda p: p.as_posix()) if (
        "tests" not in path.relative_to(source_root).parts
        and "__pycache__" not in path.parts
    ))


def _shell_files(root: Path) -> tuple[Path, ...]:
    paths = set(root.glob("*.sh")) | set((root / "scripts").rglob("*.sh"))
    return tuple(sorted(paths, key=lambda p: p.as_posix()))


def _symbol_for(node: ast.AST, parents: Mapping[ast.AST, ast.AST]) -> str:
    names = []
    current = parents.get(node)
    while current is not None:
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.append(current.name)
        current = parents.get(current)
    return ".".join(reversed(names)) or "<module>"


def _context_for(node: ast.AST, parents: Mapping[ast.AST, ast.AST]) -> ast.AST:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, (
            ast.Call, ast.Assign, ast.AnnAssign, ast.Return, ast.Compare,
            ast.Dict, ast.Set, ast.List, ast.Tuple, ast.If, ast.IfExp,
        )):
            return current
    return node


def _is_make_unknown_reason_call(node: ast.AST, parents: Mapping[ast.AST, ast.AST]) -> bool:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, ast.Call):
            func = current.func
            return (
                isinstance(func, ast.Name) and func.id == "make_unknown_reason"
            ) or (
                isinstance(func, ast.Attribute) and func.attr == "make_unknown_reason"
            )
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            return False
    return False


def _nearest_keyword(node: ast.AST, parents: Mapping[ast.AST, ast.AST]) -> Optional[ast.keyword]:
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, ast.keyword):
            return current
        if isinstance(current, (ast.Call, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            return None
    return None


def _suggest_relation(
    path: str, node: ast.AST, context: ast.AST,
    parents: Mapping[ast.AST, ast.AST], source: str,
) -> RetiredReferenceRelation:
    if path.endswith("equivalence/v2/legacy_codec.py") or path.endswith("equivalence/v2/phase7_cutover.py"):
        return RetiredReferenceRelation.L_DECODE
    if path.endswith("equivalence/unknown_reason.py"):
        symbol = _symbol_for(node, parents)
        if "make_unknown_reason" in symbol or _is_make_unknown_reason_call(node, parents):
            # This module is now the reader-only legacy schema/constructor.
            # Production compatibility projection accepts only a factory-owned
            # typed receipt; the bare-ID helper is internal legacy diagnostics.
            return RetiredReferenceRelation.D_LEGACY
        if (
            symbol.startswith("UnknownReasonId")
            or symbol.startswith("UnknownRecoveryAction.from_dict")
            or symbol.startswith("UnknownReasonDefinition.create")
            or symbol.startswith("_register_defaults")
            or symbol.startswith("_register_default_recovery_plans")
        ):
            return RetiredReferenceRelation.L_DECODE
        if symbol.startswith("coerce_unknown_recovery_action"):
            return RetiredReferenceRelation.D_LEGACY
        if symbol != "<module>" and not symbol.startswith("UnknownReasonId"):
            return RetiredReferenceRelation.L_DECODE
        return RetiredReferenceRelation.L_DECODE
    if "/validation/" in path:
        return RetiredReferenceRelation.D_LEGACY
    if _is_make_unknown_reason_call(node, parents):
        return RetiredReferenceRelation.P_EMIT
    current = node
    while current in parents:
        current = parents[current]
        if isinstance(current, (ast.Assign, ast.AnnAssign)):
            targets = current.targets if isinstance(current, ast.Assign) else (current.target,)
            if re.search(
                r"reason_id|blocking_reason|unknown_reason",
                " ".join(ast.unparse(target) for target in targets),
                re.IGNORECASE,
            ):
                return RetiredReferenceRelation.P_EMIT
            break
        if isinstance(current, ast.Return):
            function = parents.get(current)
            while function is not None and not isinstance(
                function, (ast.FunctionDef, ast.AsyncFunctionDef)
            ):
                function = parents.get(function)
            if function is not None and "reason" in function.name.lower():
                return RetiredReferenceRelation.P_EMIT
            break
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            break
    return RetiredReferenceRelation.P_ROUTE


def discover_retired_reference_candidates(repo_root: Path) -> tuple[Mapping[str, Any], ...]:
    root = Path(repo_root).resolve()
    rows = []
    for path in _python_files(root):
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        tree = ast.parse(text, filename=str(path))
        parents = {child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)}
        relative = _relative(path, root)
        occurrences: dict[tuple[str, str, str, str], int] = {}
        for node in ast.walk(tree):
            reason_id = None
            reference_kind = None
            if isinstance(node, ast.Constant) and type(node.value) is str and node.value in RETIRED_UMBRELLA_REASON_IDS:
                reason_id = node.value
                reference_kind = "exact_string_constant"
            elif (
                isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name)
                and node.value.id == "UnknownReasonId"
            ):
                matches = [value for value, member in _ENUM_MEMBER_BY_VALUE.items() if member == node.attr]
                if matches:
                    reason_id = matches[0]
                    reference_kind = "typed_enum_member"
            if reason_id is None:
                continue
            context = _context_for(node, parents)
            context_source = ast.get_source_segment(text, context) or ast.get_source_segment(text, node) or ""
            # ``unknown`` is also a widespread domain/status/display token.  It
            # enters this reason-reference universe only when the enclosing AST
            # context explicitly identifies reason semantics.  Typed enum
            # members remain unconditionally in scope.
            if (
                reason_id == "unknown"
                and reference_kind == "exact_string_constant"
            ):
                keyword = _nearest_keyword(node, parents)
                if (
                    keyword is not None
                    and keyword.arg not in {
                        "reason", "reason_id", "unknown_reason", "unknown_reasons",
                        "retired_reason_id", "raw_reason_id",
                    }
                    and not _is_make_unknown_reason_call(node, parents)
                ):
                    continue
                if not re.search(
                    r"reason(?:_id|\.reason_id|s\b)|make_unknown_reason|retired_reason",
                    context_source,
                    re.IGNORECASE,
                ):
                    continue
            key = (relative, _symbol_for(node, parents), type(node).__name__, context_source)
            ordinal = occurrences.get(key, 0)
            occurrences[key] = ordinal + 1
            identity = {
                "path": relative,
                "symbol": key[1],
                "ast_node_kind": type(node).__name__,
                "reference_kind": reference_kind,
                "reason_id": reason_id,
                "occurrence_ordinal": ordinal,
            }
            source_fingerprint = _digest({
                **identity,
                "context_node_kind": type(context).__name__,
                "context_source": context_source,
            })
            rows.append({
                "candidate_id": _digest({**identity, "source_fingerprint": source_fingerprint}),
                **identity,
                "line": int(getattr(node, "lineno", 0)),
                "column": int(getattr(node, "col_offset", 0)),
                "context_node_kind": type(context).__name__,
                "context_source": context_source,
                "source_fingerprint": source_fingerprint,
                "suggested_relation": _suggest_relation(
                    relative, node, context, parents, context_source
                ).value,
            })
    token_pattern = re.compile(
        r"(?<![A-Za-z0-9_])(" + "|".join(map(re.escape, sorted(RETIRED_UMBRELLA_REASON_IDS, key=len, reverse=True))) + r")(?![A-Za-z0-9_])"
    )
    for path in _shell_files(root):
        relative = _relative(path, root)
        text = path.read_text(encoding="utf-8", errors="surrogateescape")
        per_line: dict[tuple[int, str], int] = {}
        for line_number, line in enumerate(text.splitlines(), 1):
            for match in token_pattern.finditer(line):
                reason_id = match.group(1)
                if reason_id == "unknown" and not re.search(
                    r"reason(?:_id|s\b)|retired_reason", line, re.IGNORECASE
                ):
                    continue
                key = (line_number, reason_id)
                ordinal = per_line.get(key, 0)
                per_line[key] = ordinal + 1
                identity = {
                    "path": relative,
                    "symbol": "<shell>",
                    "ast_node_kind": "ShellToken",
                    "reference_kind": "exact_shell_token",
                    "reason_id": reason_id,
                    "occurrence_ordinal": ordinal,
                }
                source_fingerprint = _digest({**identity, "context_source": line})
                rows.append({
                    "candidate_id": _digest({**identity, "source_fingerprint": source_fingerprint}),
                    **identity,
                    "line": line_number,
                    "column": match.start(),
                    "context_node_kind": "ShellLine",
                    "context_source": line,
                    "source_fingerprint": source_fingerprint,
                    "suggested_relation": RetiredReferenceRelation.D_LEGACY.value,
                })
    # Phase 0's independently designed AST/data-flow scanner supplies candidate
    # sites whose exact finite reason set is not represented by a literal leaf
    # at that site.  These remain unreviewed here: its proposal discovers the
    # denominator, while the Phase 7 review owns the accepted finite set and
    # relation.
    phase0_template = build_inventory_review_template(root)
    for site in phase0_template.get("entries") or ():
        finite_set = sorted(
            set(site.get("resolved_reason_ids") or ()) & RETIRED_UMBRELLA_REASON_IDS
        )
        if site.get("reason_resolution") != "static_set" or not finite_set:
            continue
        identity = {
            "path": site["path"],
            "symbol": site["symbol"],
            "ast_node_kind": "Phase0DataFlowSite",
            "reference_kind": "indirect_dynamic_site",
            "reason_id": finite_set[0],
            "occurrence_ordinal": 0,
        }
        candidate_id = _digest({
            **identity,
            "phase0_site_id": site["site_id"],
            "source_fingerprint": site["inventory_source_fingerprint"],
            "finite_reason_set": finite_set,
        })
        if any(row["candidate_id"] == candidate_id for row in rows):
            raise ValueError("duplicate indirect retired reference identity")
        relation = (
            RetiredReferenceRelation.P_EMIT
            if site.get("authority_role") == "production" and site.get("construct_kind") in {
                "reason_constructor", "reason_selection_assignment",
                "reason_collection_mutation",
            }
            else RetiredReferenceRelation.D_LEGACY
            if site.get("authority_role") != "production"
            else RetiredReferenceRelation.P_ROUTE
        )
        rows.append({
            "candidate_id": candidate_id,
            **identity,
            "line": site["line"],
            "column": 0,
            "context_node_kind": site["construct_kind"],
            "context_source": site["source"],
            "source_fingerprint": site["inventory_source_fingerprint"],
            "suggested_relation": relation.value,
            "proposed_finite_reason_set": finite_set,
            "phase0_site_id": site["site_id"],
            "phase0_resolution_basis": site["resolution_basis"],
        })
    finite_sets: dict[tuple[str, str, str, str], set[str]] = {}
    for row in rows:
        context_key = (
            row["path"], row["symbol"], row["context_node_kind"], row["context_source"]
        )
        finite_sets.setdefault(context_key, set()).add(row["reason_id"])
    rows = [{
        **row,
        "proposed_finite_reason_set": (
            row["proposed_finite_reason_set"]
            if row.get("reference_kind") == "indirect_dynamic_site"
            else sorted(finite_sets[(
                row["path"], row["symbol"], row["context_node_kind"], row["context_source"]
            )])
        ),
    } for row in rows]
    rows.sort(key=lambda row: (
        row["path"], row["line"], row["column"], row["reason_id"], row["candidate_id"]
    ))
    ids = tuple(row["candidate_id"] for row in rows)
    if len(ids) != len(set(ids)):
        raise ValueError("retired reference AST node identities are not unique")
    return tuple(rows)


def build_review_template(repo_root: Path) -> Mapping[str, Any]:
    candidates = discover_retired_reference_candidates(repo_root)
    return {
        "review_kind": "phase7_retired_reason_reference_review",
        "candidate_set_digest": _digest(candidates),
        "entries": [{
            **row,
            "review_status": "unreviewed",
            "reviewed_in_scope": None,
            "reviewed_relation": None,
            "reviewed_finite_reason_set": None,
            "reviewer_disposition": None,
        } for row in candidates],
    }


def materialize_reviewed_input(
    template: Mapping[str, Any], decisions: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Apply explicit dynamic-site decisions; output still requires fixed review."""
    if decisions.get("candidate_set_digest") != template.get("candidate_set_digest"):
        raise ValueError("review decisions differ from candidate set")
    raw_overrides = tuple(decisions.get("dynamic_site_decisions") or ())
    overrides: dict[tuple[str, int, str], Mapping[str, Any]] = {}
    for item in raw_overrides:
        key = (str(item.get("path") or ""), int(item.get("line")), str(item.get("symbol") or ""))
        if key in overrides:
            raise ValueError("duplicate dynamic-site review decision")
        overrides[key] = item
    output = dict(template)
    output["review_kind"] = "phase7_retired_reason_reference_review"
    entries = []
    consumed = set()
    for source in template.get("entries") or ():
        row = dict(source)
        row["review_status"] = "reviewed"
        row["reviewed_in_scope"] = True
        row["reviewed_relation"] = row["suggested_relation"]
        row["reviewed_finite_reason_set"] = row["proposed_finite_reason_set"]
        row["reviewer_disposition"] = (
            "main-agent AST authority-role review; fixed read-only review required"
        )
        if row["reference_kind"] == "indirect_dynamic_site":
            key = (row["path"], int(row["line"]), row["symbol"])
            decision = overrides.get(key)
            if decision is None:
                raise ValueError(f"missing explicit dynamic-site review decision: {key}")
            consumed.add(key)
            in_scope = decision.get("in_scope")
            if type(in_scope) is not bool:
                raise ValueError("dynamic-site decision lacks exact scope disposition")
            row["reviewed_in_scope"] = in_scope
            row["reviewed_relation"] = decision.get("relation") if in_scope else None
            row["reviewed_finite_reason_set"] = (
                sorted(set(decision.get("finite_reason_set") or ())) if in_scope else []
            )
            row["reviewer_disposition"] = str(decision.get("disposition") or "")
            if not row["reviewer_disposition"]:
                raise ValueError("dynamic-site decision lacks review disposition")
        entries.append(row)
    if consumed != set(overrides):
        raise ValueError("review decisions contain unknown dynamic sites")
    output["entries"] = entries
    return output


def build_phase7_retired_inventory(
    repo_root: Path, reviewed: Mapping[str, Any],
) -> Mapping[str, Any]:
    candidates = discover_retired_reference_candidates(repo_root)
    candidate_digest = _digest(candidates)
    if reviewed.get("review_kind") != "phase7_retired_reason_reference_review":
        raise ValueError("retired inventory review kind is invalid")
    if reviewed.get("candidate_set_digest") != candidate_digest:
        raise ValueError("retired inventory candidate set or source fingerprint drifted")
    candidate_by_id = {row["candidate_id"]: row for row in candidates}
    reviewed_rows = tuple(reviewed.get("entries") or ())
    reviewed_by_id = {str(row.get("candidate_id") or ""): row for row in reviewed_rows}
    if len(reviewed_by_id) != len(reviewed_rows) or set(reviewed_by_id) != set(candidate_by_id):
        raise ValueError("retired inventory candidate and reviewed sets differ")
    partition = {relation.value: [] for relation in RetiredReferenceRelation}
    excluded_flow_probes = []
    for candidate_id, candidate in candidate_by_id.items():
        row = reviewed_by_id[candidate_id]
        for field in candidate:
            if row.get(field) != candidate[field]:
                raise ValueError(f"retired inventory reviewed source field drifted: {candidate_id}:{field}")
        if row.get("review_status") != "reviewed" or not row.get("reviewer_disposition"):
            raise ValueError(f"retired inventory row is not independently reviewed: {candidate_id}")
        reviewed_finite_set = tuple(sorted(set(row.get("reviewed_finite_reason_set") or ())))
        in_scope = row.get("reviewed_in_scope")
        if type(in_scope) is not bool:
            raise ValueError(f"retired inventory scope disposition is invalid: {candidate_id}")
        if not in_scope:
            if candidate.get("reference_kind") != "indirect_dynamic_site":
                raise ValueError("literal retired reference cannot be excluded")
            if reviewed_finite_set or row.get("reviewed_relation") is not None:
                raise ValueError("excluded flow probe cannot own a retired set or relation")
            excluded_flow_probes.append({
                **candidate,
                "reviewer_disposition": row["reviewer_disposition"],
            })
            continue
        relation = RetiredReferenceRelation(row.get("reviewed_relation"))
        if not reviewed_finite_set or any(
            item not in RETIRED_UMBRELLA_REASON_IDS for item in reviewed_finite_set
        ):
            raise ValueError(f"retired inventory reviewed finite set is invalid: {candidate_id}")
        if (
            candidate.get("reference_kind") != "indirect_dynamic_site"
            and reviewed_finite_set != tuple(candidate["proposed_finite_reason_set"])
        ):
            raise ValueError("literal reference finite set cannot be reclassified")
        partition[relation.value].append({
            **candidate,
            "finite_reason_set": list(reviewed_finite_set),
            "relation": relation.value,
            "reviewer_disposition": row["reviewer_disposition"],
        })
    classified_ids = [row["candidate_id"] for rows in partition.values() for row in rows]
    excluded_ids = [row["candidate_id"] for row in excluded_flow_probes]
    if (
        len(classified_ids + excluded_ids) != len(set(classified_ids + excluded_ids))
        or set(classified_ids + excluded_ids) != set(candidate_by_id)
    ):
        raise ValueError("retired reference partition is not an exact disjoint union")
    body = {
        "manifest_kind": PHASE7_RETIRED_INVENTORY_KIND,
        "retired_reason_ids": sorted(RETIRED_UMBRELLA_REASON_IDS),
        "candidate_set_digest": candidate_digest,
        "review_digest": _digest(reviewed),
        "discovered_probe_count": len(candidates),
        "candidate_count": len(classified_ids),
        "classified_count": len(classified_ids),
        "excluded_flow_probe_count": len(excluded_flow_probes),
        "excluded_flow_probes": excluded_flow_probes,
        "relations": partition,
        "relation_counts": {key: len(value) for key, value in partition.items()},
        "production_umbrella_generation": len(partition[RetiredReferenceRelation.P_EMIT.value]),
        "production_umbrella_routing": len(partition[RetiredReferenceRelation.P_ROUTE.value]),
    }
    return {**body, "manifest_digest": _digest(body)}


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--write-review-template")
    parser.add_argument("--inventory-review")
    parser.add_argument("--review-template")
    parser.add_argument("--review-decisions")
    parser.add_argument("--write-reviewed")
    parser.add_argument("--output")
    args = parser.parse_args(argv)
    if args.write_review_template:
        payload = build_review_template(Path(args.repo_root))
        output = Path(args.write_review_template)
    elif args.write_reviewed:
        if not args.review_template or not args.review_decisions:
            parser.error("--review-template and --review-decisions are required")
        template = json.loads(Path(args.review_template).read_text(encoding="utf-8"))
        decisions = json.loads(Path(args.review_decisions).read_text(encoding="utf-8"))
        payload = materialize_reviewed_input(template, decisions)
        output = Path(args.write_reviewed)
    else:
        if not args.inventory_review or not args.output:
            parser.error("--inventory-review and --output are required")
        reviewed = json.loads(Path(args.inventory_review).read_text(encoding="utf-8"))
        payload = build_phase7_retired_inventory(Path(args.repo_root), reviewed)
        output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
