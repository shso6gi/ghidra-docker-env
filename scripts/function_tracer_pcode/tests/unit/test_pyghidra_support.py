from pathlib import Path
from unittest.mock import Mock

from scripts.function_tracer_pcode.cli._pyghidra_support import start_headless_pyghidra


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
