import os
import tempfile
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.ghidra.pyghidra_support import (
    load_pyghidra,
    start_headless_pyghidra,
)
from scripts.function_tracer_pcode.cli.commands.equivalence import (
    ProgramImportError,
    _emit_import_error_result,
    _load_program_context,
    _to_java_byte_array,
)
from scripts.function_tracer_pcode.config.settings import apply_runtime_environment


class _LoadContext:
    def __init__(self, value):
        self.value = value
        self.closed = False

    def __enter__(self):
        return self.value

    def __exit__(self, exc_type, exc, tb):
        self.closed = True


class _FailingLoadContext:
    def __enter__(self):
        raise OSError("No such file or directory")

    def __exit__(self, exc_type, exc, tb):
        return False


class _Builder:
    def __init__(self, fake_pyghidra, should_fail_file_load):
        self.fake_pyghidra = fake_pyghidra
        self.should_fail_file_load = should_fail_file_load
        self.source_value = None

    def project(self, project):
        return self

    def source(self, source_value):
        self.source_value = source_value
        self.fake_pyghidra.sources.append(source_value)
        return self

    def name(self, value):
        return self

    def load(self):
        if isinstance(self.source_value, str) and self.should_fail_file_load:
            return _FailingLoadContext()
        source_kind = "path" if isinstance(self.source_value, str) else "bytes"
        return _LoadContext(f"loaded:{source_kind}")


class _FakePyGhidra:
    def __init__(self, *, should_fail_file_load):
        self.should_fail_file_load = should_fail_file_load
        self.sources = []

    def program_loader(self):
        return _Builder(self, self.should_fail_file_load)


def test_load_program_context_retries_with_bytes_when_file_provider_fails(tmp_path):
    binary = tmp_path / "sample.bin"
    binary.write_bytes(b"\x7fELFdemo")
    fake_pyghidra = _FakePyGhidra(should_fail_file_load=True)

    cm, result = _load_program_context(
        fake_pyghidra,
        object(),
        str(binary),
        "binary1",
        quiet=True,
    )

    assert result == "loaded:bytes"
    assert fake_pyghidra.sources[0] == str(binary)
    assert bytes(fake_pyghidra.sources[1]) == b"\x7fELFdemo"
    cm.__exit__(None, None, None)


def test_load_program_context_reports_diagnostics_for_missing_file(tmp_path):
    fake_pyghidra = _FakePyGhidra(should_fail_file_load=True)
    missing = tmp_path / "missing.bin"

    with pytest.raises(ProgramImportError) as exc_info:
        _load_program_context(
            fake_pyghidra,
            object(),
            str(missing),
            "binary1",
            quiet=True,
        )

    message = str(exc_info.value)
    assert "source is not a regular file" in message
    assert "exists=False" in message


def test_emit_import_error_result_outputs_error_line_and_json(capsys):
    args = SimpleNamespace(
        output=None,
        quiet=False,
        verbose=False,
        debug=False,
        emit_result_json=True,
    )

    with pytest.raises(SystemExit) as exc_info:
        _emit_import_error_result(
            args,
            binary1_path="/tmp/left",
            binary2_path="/tmp/right",
            func_name1="f",
            func_name2="f",
            error_message="import failed",
            start_time=0.0,
        )

    assert exc_info.value.code == 4
    output = capsys.readouterr().out
    assert "Result: ERROR" in output
    assert "ERROR: import failed" in output
    assert "=== EQUIVALENCE_RESULT_JSON_BEGIN ===" in output
    assert '"error_message": "import failed"' in output


@pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="real PyGhidra import smoke is opt-in; set RUN_PYGHIDRA_REGRESSIONS=1",
)
def test_real_pyghidra_accepts_byte_array_source_for_existing_elf():
    pytest.importorskip("pyghidra")
    repo_root = Path(__file__).resolve().parents[4]
    binary = (
        repo_root
        / "targets"
        / "EqBench"
        / "benchmarks"
        / "REVE"
        / "barthe2"
        / "Eq"
        / "source"
        / "newV-arm64-clang-O0"
    )
    if not binary.is_file():
        pytest.skip(f"fixture binary not found: {binary}")

    pyghidra = load_pyghidra()
    runtime_env = apply_runtime_environment()
    try:
        start_headless_pyghidra(
            pyghidra,
            install_dir=Path(runtime_env.ghidra_install_dir)
            if runtime_env.ghidra_install_dir
            else None,
        )
    except Exception as exc:
        pytest.skip(f"PyGhidra startup failed: {exc}")

    with tempfile.TemporaryDirectory() as temp_dir:
        with pyghidra.open_project(temp_dir, "byte-source-smoke", create=True) as project:
            with (
                pyghidra.program_loader()
                .project(project)
                .source(_to_java_byte_array(binary.read_bytes()))
                .name("binary-bytes")
                .load()
            ) as result:
                program = result.getPrimaryDomainObject()
                assert program.getName() == "binary-bytes"
