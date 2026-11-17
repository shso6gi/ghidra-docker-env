# -*- coding: utf-8 -*-
"""Record concrete-run traces and compiler-spec facts as test fixtures.

Needs PyGhidra (run it in the container).  Each run goes through
``ghidra.concrete_worker.run_isolated`` -- the same child-process path and
the same executor as production -- with recording on, and is written as one
``concrete-run-trace-v1`` file (``concrete/recording.py``).  The fixture's
binary is named relative to ``--bench-root`` and identified by its SHA-256;
binaries are never copied into the repository.

Example::

    python3 -B -m scripts.function_tracer_pcode.tests.tools.record_concrete_fixture \\
      --bench-root targets/EqBench/benchmarks \\
      --binary REVE/ackermann/Eq/source/newV-arm64-gcc-O0 --function f \\
      --set x0=1 --set x1=1 --observe x0 --fixture-id arm64_ackermann_returned \\
      --output-dir scripts/function_tracer_pcode/tests/fixtures/concrete

``--set REGISTER=VALUE[:BYTES]`` writes VALUE (a register image, taken as
given) to the low BYTES bytes of REGISTER; ``--facts-only`` writes the
program's compiler-spec facts instead of running anything.
"""

from __future__ import annotations

import argparse
import json
import os
import sys

from scripts.function_tracer_pcode.concrete.abi import AbiId, abi_model
from scripts.function_tracer_pcode.concrete.executor import ExecutionRequest, build_entry_state
from scripts.function_tracer_pcode.concrete.input_surface import RegisterImage
from scripts.function_tracer_pcode.ghidra.concrete_worker import run_isolated


def _parse_set(text: str):
    register, _, rest = text.partition("=")
    value, _, count = rest.partition(":")
    return register, int(value, 0), int(count) if count else None


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--bench-root", required=True)
    parser.add_argument("--binary", required=True, help="path relative to --bench-root")
    parser.add_argument("--function", required=True)
    parser.add_argument("--set", action="append", default=[])
    parser.add_argument("--observe", action="append", default=[])
    parser.add_argument("--step-limit", type=int, default=100_000)
    parser.add_argument("--fixture-id", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--facts-only", action="store_true")
    parser.add_argument("--timeout", type=float, default=600.0)
    args = parser.parse_args(argv)

    path = os.path.join(args.bench_root, args.binary)
    opened = run_isolated(path, [], timeout_seconds=args.timeout, resolve_functions=[args.function])
    if opened.facts is None:
        print(f"no facts: {opened.exit} {opened.refusal} {opened.stderr_tail[-500:]}", file=sys.stderr)
        return 1
    os.makedirs(args.output_dir, exist_ok=True)
    if args.facts_only:
        record = {
            "schema": "concrete-compiler-spec-facts-v1",
            "binary": args.binary,
            "refusal": opened.refusal,
            "facts": opened.facts["compiler_spec"],
        }
        with open(os.path.join(args.output_dir, f"{args.fixture_id}.json"), "w") as handle:
            json.dump(record, handle, indent=1, sort_keys=True)
            handle.write("\n")
        return 0
    if opened.refusal is not None:
        print(f"refused: {opened.refusal}", file=sys.stderr)
        return 1
    entry = opened.functions.get(args.function)
    if entry is None:
        print(f"no unique function {args.function!r}", file=sys.stderr)
        return 1
    abi = abi_model(AbiId(opened.facts["abi_id"]))
    images = []
    for text in args.set:
        register, value, count = _parse_set(text)
        images.append(RegisterImage(register, count or 8, value))
    request = ExecutionRequest(
        entry, build_entry_state(abi, entry, tuple(images)), tuple(args.observe), args.step_limit
    )
    run = run_isolated(path, [request], timeout_seconds=args.timeout, options={"record": True})
    trace = run.traces[0]
    if trace is None:
        print(f"no trace: {run.exit} {run.results[0]} {run.stderr_tail[-500:]}", file=sys.stderr)
        return 1
    trace = dict(trace)
    trace["provenance"] = dict(trace["provenance"], binary=args.binary, function=args.function)
    with open(os.path.join(args.output_dir, f"{args.fixture_id}.json"), "w") as handle:
        json.dump(trace, handle, separators=(",", ":"), sort_keys=True)
        handle.write("\n")
    print(json.dumps(trace["result"])[:400])
    return 0


if __name__ == "__main__":
    sys.exit(main())
