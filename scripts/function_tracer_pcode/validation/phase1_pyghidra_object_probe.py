# -*- coding: utf-8 -*-
"""Collect small Phase 1 object-evidence facts with PyGhidra.

The output is intentionally narrow: function entry offsets and CALL/CALLIND
P-code operations from ``HighFunction`` objects.  It is used to back Phase 1
manifests without parsing decompiler text or validation log prose.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import tempfile
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from ..cli._pyghidra_support import load_pyghidra, start_headless_pyghidra
from ..config import apply_runtime_environment


def collect_object_facts(
    *,
    binaries: Mapping[str, Path],
    functions: Sequence[str],
    timeout_seconds: int = 60,
) -> Dict[str, Dict[str, Any]]:
    """Return object-derived callsite facts keyed by binary id and function."""

    pyghidra = load_pyghidra()
    runtime_env = apply_runtime_environment()
    start_headless_pyghidra(
        pyghidra,
        install_dir=(
            Path(runtime_env.ghidra_install_dir)
            if runtime_env.ghidra_install_dir
            else None
        ),
    )

    from ghidra.app.decompiler import DecompInterface
    from ghidra.util.task import ConsoleTaskMonitor

    result: Dict[str, Dict[str, Any]] = {}
    for binary_id, binary_path in sorted(binaries.items()):
        with tempfile.TemporaryDirectory() as temp_dir:
            with pyghidra.open_project(temp_dir, "Phase1ObjectProbe", create=True) as project:
                loader = pyghidra.program_loader().project(project).source(str(binary_path))
                with loader.load() as load_result:
                    program = load_result.getPrimaryDomainObject()
                    pyghidra.analyze(program)
                    decompiler = DecompInterface()
                    decompiler.openProgram(program)
                    function_manager = program.getFunctionManager()
                    all_functions = list(function_manager.getFunctions(True))
                    by_name = {fn.getName(): fn for fn in all_functions}
                    result[binary_id] = {
                        name: _collect_function_facts(
                            program=program,
                            function_manager=function_manager,
                            decompiler=decompiler,
                            function=by_name[name],
                            timeout_seconds=timeout_seconds,
                        )
                        for name in functions
                    }
    return result


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Collect Phase 1 PyGhidra object facts.")
    parser.add_argument(
        "--binary",
        action="append",
        required=True,
        metavar="ID=PATH",
        help="Binary id and path, e.g. B13=targets/.../function_call_test-mips64-gcc-O0",
    )
    parser.add_argument("--function", action="append", required=True, help="Function name to inspect")
    parser.add_argument("--output", required=True, help="Output JSON path")
    parser.add_argument("--timeout-seconds", type=int, default=60)
    args = parser.parse_args(argv)

    facts = collect_object_facts(
        binaries=dict(_parse_binary_arg(item) for item in args.binary),
        functions=list(args.function),
        timeout_seconds=args.timeout_seconds,
    )
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(facts, indent=2, sort_keys=True) + "\n")
    print(output)
    print(_sha256_file(output))
    return 0


def _collect_function_facts(
    *,
    program: Any,
    function_manager: Any,
    decompiler: Any,
    function: Any,
    timeout_seconds: int,
) -> Dict[str, Any]:
    from ghidra.util.task import ConsoleTaskMonitor

    decompiled = decompiler.decompileFunction(function, timeout_seconds, ConsoleTaskMonitor())
    high_function = decompiled.getHighFunction()
    calls = []
    ops = high_function.getPcodeOps()
    while ops.hasNext():
        op = ops.next()
        mnemonic = op.getMnemonic()
        if mnemonic not in {"CALL", "CALLIND"}:
            continue
        calls.append(
            {
                "mnemonic": mnemonic,
                "target": _call_target_name(op, function_manager),
                "address_offset": op.getSeqnum().getTarget().getOffset(),
                "seq_order": op.getSeqnum().getOrder(),
                "inputs": [
                    _varnode_input_fact(program, op.getInput(index), index)
                    for index in range(op.getNumInputs())
                ],
            }
        )
    return {
        "entry_offset": function.getEntryPoint().getOffset(),
        "call_count": len(calls),
        "calls": calls,
    }


def _call_target_name(op: Any, function_manager: Any) -> Optional[str]:
    if op.getMnemonic() != "CALL" or op.getNumInputs() <= 0:
        return None
    target_function = function_manager.getFunctionAt(op.getInput(0).getAddress())
    if target_function is not None:
        return target_function.getName()
    return str(op.getInput(0).getAddress())


def _varnode_input_fact(program: Any, varnode: Any, index: int) -> Dict[str, Any]:
    address = varnode.getAddress() if varnode is not None else None
    register_name = None
    if varnode is not None and varnode.isRegister():
        register = program.getRegister(address, varnode.getSize())
        register_name = register.getName() if register is not None else None
    return {
        "index": index,
        "space": address.getAddressSpace().getName() if address is not None else None,
        "offset": address.getOffset() if address is not None else None,
        "size": varnode.getSize() if varnode is not None else None,
        "register_name": register_name,
        "is_constant": varnode.isConstant() if varnode is not None else None,
        "is_register": varnode.isRegister() if varnode is not None else None,
    }


def _parse_binary_arg(value: str) -> Tuple[str, Path]:
    binary_id, separator, path = value.partition("=")
    if not separator or not binary_id or not path:
        raise ValueError(f"expected binary argument in ID=PATH form, got {value!r}")
    return binary_id, Path(path)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
