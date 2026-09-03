"""Typed EqBench source-to-binary build provenance receipts."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
from typing import Any, Mapping, Sequence

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.reporting.execution_identity import sha256_file


SCHEMA = "eqbench-build-receipt-v1"
AUTHORITY_KIND = "EqBenchSourceBinaryBuildReceipt"
PROVENANCE_KINDS = frozenset({"FRESH_COMPILE", "ADOPTED_PREBUILT"})
BINARY_IDS = tuple(f"B{index}" for index in range(1, 17))
ARCH = {**{f"B{i}": "arm64" for i in range(1, 9)},
        **{f"B{i}": "mips64" for i in range(9, 17)}}
COMPILER = {
    **{f"B{i}": "clang" for i in range(1, 5)},
    **{f"B{i}": "gcc" for i in range(5, 9)},
    **{f"B{i}": "clang" for i in range(9, 13)},
    **{f"B{i}": "gcc" for i in range(13, 17)},
}
OPTIMIZATION = {f"B{i}": f"O{(i - 1) % 4}" for i in range(1, 17)}


def _relative_file(repo_root: Path, path: Path) -> str:
    absolute = path.resolve(strict=True)
    try:
        return absolute.relative_to(repo_root.resolve()).as_posix()
    except ValueError as exc:
        raise ValueError(f"build input is outside repository: {absolute}") from exc


def _output_kind(source_path: Path) -> str:
    text = source_path.read_text(encoding="utf-8", errors="ignore")
    return "executable" if re.search(r"(^|\s)main\s*\(", text) else "object"


def _compiler_command(binary_id: str) -> tuple[str, tuple[str, ...]]:
    arch = ARCH[binary_id]
    compiler = COMPILER[binary_id]
    if (arch, compiler) == ("arm64", "gcc"):
        return "aarch64-linux-gnu-gcc", ("-march=armv8-a",)
    if (arch, compiler) == ("arm64", "clang"):
        return "clang", ("--target=aarch64-linux-gnu", "-march=armv8-a")
    if (arch, compiler) == ("mips64", "gcc"):
        return "mips64-linux-gnuabi64-gcc", ("-mabi=64",)
    return "clang", ("--target=mips64-linux-gnuabi64", "-mabi=64")


def _argv(binary_id: str, source_name: str, output_name: str, output_kind: str) -> list[str]:
    executable, arch_args = _compiler_command(binary_id)
    argv = [executable, *arch_args, f"-{OPTIMIZATION[binary_id]}"]
    if output_kind == "object":
        argv.append("-c")
    return [*argv, source_name, "-o", output_name]


def _toolchain_identity(executable: str, *, fresh: bool) -> Mapping[str, Any]:
    if not fresh:
        return {
            "executable_requested": executable,
            "identity_status": "UNAVAILABLE_FOR_ADOPTED_PREBUILT",
            "resolved_path": None,
            "executable_sha256": None,
            "version_argv": [executable, "--version"],
            "version_stdout_sha256": None,
        }
    resolved = shutil.which(executable)
    if resolved is None:
        raise ValueError(f"fresh build toolchain is unavailable: {executable}")
    version = subprocess.run(
        (executable, "--version"), check=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    ).stdout
    return {
        "executable_requested": executable,
        "identity_status": "RESOLVED",
        "resolved_path": str(Path(resolved).resolve()),
        "executable_sha256": sha256_file(Path(resolved).resolve()),
        "version_argv": [executable, "--version"],
        "version_stdout_sha256": hashlib.sha256(version).hexdigest(),
    }


def build_receipt(
    repo_root: Path, *, sample_identity: str, source_path: Path,
    compile_script_path: Path, binary_root: Path, target_binary_root: Path,
    binary_ids: Sequence[str], provenance_kind: str,
) -> Mapping[str, Any]:
    repo_root = repo_root.resolve()
    if provenance_kind not in PROVENANCE_KINDS:
        raise ValueError("EqBench build provenance kind is invalid")
    ids = tuple(binary_ids)
    if not ids or len(ids) != len(set(ids)) or any(item not in BINARY_IDS for item in ids):
        raise ValueError("EqBench build binary ID census is invalid")
    ids = tuple(item for item in BINARY_IDS if item in ids)
    source_relative = _relative_file(repo_root, source_path)
    compile_relative = _relative_file(repo_root, compile_script_path)
    source_name = source_path.name
    source_base = source_path.stem
    output_kind = _output_kind(source_path)
    fresh = provenance_kind == "FRESH_COMPILE"
    toolchains: dict[str, Mapping[str, Any]] = {}
    axes = []
    for binary_id in ids:
        executable, _ = _compiler_command(binary_id)
        if executable not in toolchains:
            toolchains[executable] = _toolchain_identity(executable, fresh=fresh)
        output_name = (
            f"{source_base}-{ARCH[binary_id]}-{COMPILER[binary_id]}-"
            f"{OPTIMIZATION[binary_id]}"
        )
        built = binary_root / output_name
        target = target_binary_root / output_name
        if not built.is_file():
            raise ValueError(f"EqBench build output is missing: {built}")
        try:
            target_relative = target.resolve().relative_to(repo_root).as_posix()
        except ValueError as exc:
            raise ValueError("EqBench target binary path is outside repository") from exc
        axes.append({
            "binary_id": binary_id,
            "binary_path": target_relative,
            "binary_sha256": sha256_file(built),
            "arch": ARCH[binary_id],
            "compiler": COMPILER[binary_id],
            "optimization": OPTIMIZATION[binary_id],
            "compiler_executable": executable,
            "compiler_argv": _argv(binary_id, source_name, output_name, output_kind),
        })
    body = {
        "schema": SCHEMA,
        "authority_kind": AUTHORITY_KIND,
        "provenance_kind": provenance_kind,
        "sample_identity": sample_identity,
        "source_path": source_relative,
        "source_sha256": sha256_file(source_path),
        "compile_script_path": compile_relative,
        "compile_script_sha256": sha256_file(compile_script_path),
        "compile_script_argv": ["./compile_all.sh", source_name],
        "output_kind": output_kind,
        "binary_axes": axes,
        "toolchains": dict(sorted(toolchains.items())),
    }
    return {**body, "receipt_digest": authority_digest(body)}


def validate_receipt(
    payload: Mapping[str, Any], *, repo_root: Path,
    required_binary_ids: Sequence[str], require_fresh: bool = False,
) -> Mapping[str, Any]:
    fields = {
        "schema", "authority_kind", "provenance_kind", "sample_identity",
        "source_path", "source_sha256", "compile_script_path",
        "compile_script_sha256", "compile_script_argv", "output_kind",
        "binary_axes", "toolchains", "receipt_digest",
    }
    if not isinstance(payload, Mapping) or set(payload) != fields:
        raise ValueError("EqBench build receipt schema differs")
    body = {key: payload[key] for key in fields - {"receipt_digest"}}
    if (
        payload["schema"] != SCHEMA
        or payload["authority_kind"] != AUTHORITY_KIND
        or payload["provenance_kind"] not in PROVENANCE_KINDS
        or (require_fresh and payload["provenance_kind"] != "FRESH_COMPILE")
        or payload["receipt_digest"] != authority_digest(body)
        or type(payload["binary_axes"]) is not list
        or type(payload["toolchains"]) is not dict
    ):
        raise ValueError("EqBench build receipt body is invalid")
    repo_root = repo_root.resolve()
    source = repo_root / payload["source_path"]
    compile_script = repo_root / payload["compile_script_path"]
    if (
        Path(payload["source_path"]).is_absolute()
        or ".." in Path(payload["source_path"]).parts
        or Path(payload["compile_script_path"]).is_absolute()
        or ".." in Path(payload["compile_script_path"]).parts
        or not source.is_file() or sha256_file(source) != payload["source_sha256"]
        or not compile_script.is_file()
        or sha256_file(compile_script) != payload["compile_script_sha256"]
        or payload["output_kind"] != _output_kind(source)
        or payload["compile_script_argv"] != ["./compile_all.sh", source.name]
    ):
        raise ValueError("EqBench build source or compile script drifted")
    axes = {row.get("binary_id"): row for row in payload["binary_axes"] if isinstance(row, Mapping)}
    if len(axes) != len(payload["binary_axes"]):
        raise ValueError("EqBench build axis identities differ")
    required = tuple(required_binary_ids)
    if any(item not in BINARY_IDS for item in required) or not set(required) <= set(axes):
        raise ValueError("EqBench build receipt lacks required binary axes")
    expected_toolchains = {_compiler_command(binary_id)[0] for binary_id in axes}
    if set(payload["toolchains"]) != expected_toolchains:
        raise ValueError("EqBench build toolchain census differs")
    toolchain_fields = {
        "executable_requested", "identity_status", "resolved_path",
        "executable_sha256", "version_argv", "version_stdout_sha256",
    }
    for executable, toolchain in payload["toolchains"].items():
        if (
            not isinstance(toolchain, Mapping) or set(toolchain) != toolchain_fields
            or toolchain["executable_requested"] != executable
            or toolchain["version_argv"] != [executable, "--version"]
        ):
            raise ValueError("EqBench build toolchain identity differs")
        if payload["provenance_kind"] == "FRESH_COMPILE":
            if (
                toolchain["identity_status"] != "RESOLVED"
                or not all(
                    isinstance(toolchain[field], str) and toolchain[field]
                    for field in (
                        "resolved_path", "executable_sha256",
                        "version_stdout_sha256",
                    )
                )
            ):
                raise ValueError("fresh EqBench toolchain identity is incomplete")
        elif (
            toolchain["identity_status"] != "UNAVAILABLE_FOR_ADOPTED_PREBUILT"
            or any(toolchain[field] is not None for field in (
                "resolved_path", "executable_sha256", "version_stdout_sha256",
            ))
        ):
            raise ValueError("adopted EqBench toolchain identity is invalid")
    for binary_id, row in axes.items():
        executable, _ = _compiler_command(binary_id)
        output_name = Path(row.get("binary_path", "")).name
        expected_fields = {
            "binary_id", "binary_path", "binary_sha256", "arch", "compiler",
            "optimization", "compiler_executable", "compiler_argv",
        }
        binary = repo_root / str(row.get("binary_path", ""))
        if (
            set(row) != expected_fields
            or row["arch"] != ARCH[binary_id]
            or row["compiler"] != COMPILER[binary_id]
            or row["optimization"] != OPTIMIZATION[binary_id]
            or row["compiler_executable"] != executable
            or row["compiler_argv"] != _argv(
                binary_id, source.name, output_name, payload["output_kind"]
            )
            or Path(row["binary_path"]).is_absolute()
            or ".." in Path(row["binary_path"]).parts
            or not binary.is_file()
            or sha256_file(binary) != row["binary_sha256"]
        ):
            raise ValueError(f"EqBench build axis drifted: {binary_id}")
    return body


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--receipt", required=True)
    parser.add_argument("--materialize", action="store_true")
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--require-fresh", action="store_true")
    parser.add_argument("--provenance-kind", choices=sorted(PROVENANCE_KINDS))
    parser.add_argument("--sample-identity")
    parser.add_argument("--source")
    parser.add_argument("--compile-script")
    parser.add_argument("--binary-root")
    parser.add_argument("--target-binary-root")
    parser.add_argument("--binary-id", action="append", default=[])
    args = parser.parse_args(argv)
    repo_root = Path(args.repo_root).resolve()
    receipt = Path(args.receipt)
    if args.materialize:
        required = (
            args.provenance_kind, args.sample_identity, args.source,
            args.compile_script, args.binary_root, args.target_binary_root,
        )
        if any(value is None for value in required) or not args.binary_id:
            parser.error("build receipt materialization requires every build input")
        payload = build_receipt(
            repo_root, sample_identity=args.sample_identity,
            source_path=Path(args.source), compile_script_path=Path(args.compile_script),
            binary_root=Path(args.binary_root),
            target_binary_root=Path(args.target_binary_root),
            binary_ids=args.binary_id, provenance_kind=args.provenance_kind,
        )
        receipt.parent.mkdir(parents=True, exist_ok=True)
        temporary = receipt.with_suffix(receipt.suffix + ".new")
        temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        temporary.replace(receipt)
    elif args.validate:
        payload = json.loads(receipt.read_text(encoding="utf-8"))
        validate_receipt(
            payload, repo_root=repo_root, required_binary_ids=args.binary_id,
            require_fresh=args.require_fresh,
        )
    else:
        parser.error("choose --materialize or --validate")
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
