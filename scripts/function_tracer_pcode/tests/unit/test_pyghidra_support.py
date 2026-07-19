import os
from pathlib import Path
from unittest.mock import Mock

from scripts.function_tracer_pcode.cli._pyghidra_support import (
    _ensure_headless_ghidra_user_dirs,
    start_headless_pyghidra,
)


def test_ensure_headless_ghidra_user_dirs_uses_per_process_paths(monkeypatch, tmp_path):
    registered_cleanups = []
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.cli._pyghidra_support.tempfile.gettempdir",
        lambda: str(tmp_path),
    )
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.cli._pyghidra_support.atexit.register",
        lambda function, *args, **kwargs: registered_cleanups.append(
            (function, args, kwargs)
        ),
    )
    monkeypatch.setattr("scripts.function_tracer_pcode.cli._pyghidra_support.os.getpid", lambda: 4242)
    monkeypatch.delenv("XDG_CONFIG_HOME", raising=False)
    monkeypatch.delenv("XDG_CACHE_HOME", raising=False)

    _ensure_headless_ghidra_user_dirs()

    expected_base = tmp_path / "codex-ghidra" / "pid-4242"
    assert Path(os.environ["XDG_CONFIG_HOME"]) == expected_base / "config"
    assert Path(os.environ["XDG_CACHE_HOME"]) == expected_base / "cache"
    assert (expected_base / "config").is_dir()
    assert (expected_base / "cache").is_dir()
    assert len(registered_cleanups) == 1

    cleanup, args, kwargs = registered_cleanups[0]
    cleanup(*args, **kwargs)
    assert not expected_base.exists()


def test_ensure_headless_ghidra_user_dirs_overrides_shared_environment(monkeypatch, tmp_path):
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.cli._pyghidra_support.tempfile.gettempdir",
        lambda: str(tmp_path),
    )
    monkeypatch.setattr("scripts.function_tracer_pcode.cli._pyghidra_support.os.getpid", lambda: 17)
    monkeypatch.setenv("XDG_CONFIG_HOME", "/tmp/shared-ghidra-config")
    monkeypatch.setenv("XDG_CACHE_HOME", "/tmp/shared-ghidra-cache")

    _ensure_headless_ghidra_user_dirs()

    expected_base = tmp_path / "codex-ghidra" / "pid-17"
    assert Path(os.environ["XDG_CONFIG_HOME"]) == expected_base / "config"
    assert Path(os.environ["XDG_CACHE_HOME"]) == expected_base / "cache"


def test_start_headless_pyghidra_falls_back_to_module_start(monkeypatch):
    monkeypatch.delenv("XDG_CONFIG_HOME", raising=False)
    monkeypatch.delenv("XDG_CACHE_HOME", raising=False)

    pyghidra = Mock()
    pyghidra.start = Mock()
    pyghidra.HeadlessPyGhidraLauncher = None

    start_headless_pyghidra(pyghidra, install_dir=Path("/tmp/ghidra"))

    pyghidra.start.assert_called_once_with(install_dir=Path("/tmp/ghidra"))


def test_start_headless_pyghidra_uses_headless_launcher_when_available(monkeypatch):
    monkeypatch.delenv("XDG_CONFIG_HOME", raising=False)
    monkeypatch.delenv("XDG_CACHE_HOME", raising=False)

    started = {"value": False}
    launcher_instances = []

    class FakeLauncher:
        def __init__(self, verbose=False, install_dir=None):
            self.verbose = verbose
            self.install_dir = install_dir
            launcher_instances.append(self)

        def uninstall_plugin(self, _name):
            return None

        def start(self):
            started["value"] = True

    pyghidra = Mock()
    pyghidra.HeadlessPyGhidraLauncher = FakeLauncher
    pyghidra.start = Mock()

    start_headless_pyghidra(pyghidra, install_dir=Path("/tmp/local-ghidra"))

    assert started["value"] is True
    assert len(launcher_instances) == 1
    launcher = launcher_instances[0]
    assert launcher.install_dir == Path("/tmp/local-ghidra")
    assert hasattr(launcher._pre_launch_init, "__self__")
    assert launcher._pre_launch_init.__self__ is launcher
    pyghidra.start.assert_not_called()
