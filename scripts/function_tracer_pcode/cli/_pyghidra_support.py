# -*- coding: utf-8 -*-
"""Typed runtime accessors for the optional pyghidra dependency."""

from __future__ import annotations

import os
import tempfile
from importlib import import_module
from pathlib import Path
from types import MethodType
from typing import Any, ContextManager, Optional, Protocol, cast


class _DomainObject(Protocol):
    def getName(self) -> Optional[str]:
        ...


class _LoadResult(Protocol):
    def getPrimaryDomainObject(self) -> _DomainObject:
        ...


class _LoaderContext(ContextManager[_LoadResult], Protocol):
    ...


class _ProgramLoaderBuilder(Protocol):
    def project(self, project: Any) -> "_ProgramLoaderBuilder":
        ...

    def source(self, path: str) -> "_ProgramLoaderBuilder":
        ...

    def name(self, value: str) -> "_ProgramLoaderBuilder":
        ...

    def load(self) -> _LoaderContext:
        ...


class _ProjectContext(ContextManager[Any], Protocol):
    ...


class PyGhidraModule(Protocol):
    def start(self, *, install_dir: Optional[Path] = None) -> None:
        ...

    def open_project(self, path: str, name: str, *, create: bool = False) -> _ProjectContext:
        ...

    def program_loader(self) -> _ProgramLoaderBuilder:
        ...

    def analyze(self, program: Any) -> None:
        ...


def load_pyghidra() -> PyGhidraModule:
    """Import pyghidra with an explicit protocol for type checkers."""
    return cast(PyGhidraModule, import_module("pyghidra"))


def _ensure_headless_ghidra_user_dirs() -> None:
    """Provide writable per-process XDG locations for headless Ghidra sessions."""
    base_dir = Path(tempfile.gettempdir()) / "codex-ghidra" / f"pid-{os.getpid()}"
    config_dir = base_dir / "config"
    cache_dir = base_dir / "cache"

    config_dir.mkdir(parents=True, exist_ok=True)
    cache_dir.mkdir(parents=True, exist_ok=True)

    # Parallel equivalence runs launch multiple isolated Python/JVM processes.
    # Sharing a single Ghidra XDG/cache root across those processes can race on
    # filesystem caches such as ``fscache2`` and yield flaky behavior.
    os.environ["XDG_CONFIG_HOME"] = str(config_dir)
    os.environ["XDG_CACHE_HOME"] = str(cache_dir)


def _install_headless_pre_launch_hook(launcher: Any) -> None:
    """Trim PyGhidra's UI plugin bootstrap, which is fragile in headless sandboxes."""

    def _pre_launch_init_without_ui_plugins(self) -> None:
        from ghidra import GhidraApplicationLayout, GhidraLauncher

        self._layout = GhidraApplicationLayout()
        self.uninstall_plugin("pyhidra")
        self._layout = GhidraLauncher.initializeGhidraEnvironment()

    launcher._pre_launch_init = MethodType(_pre_launch_init_without_ui_plugins, launcher)


def start_headless_pyghidra(pyghidra: PyGhidraModule, *, install_dir: Optional[Path] = None) -> None:
    """Start PyGhidra on a headless-safe path that avoids GUI plugin bootstrap."""

    _ensure_headless_ghidra_user_dirs()

    launcher_cls = getattr(pyghidra, "HeadlessPyGhidraLauncher", None)
    if launcher_cls is None:
        pyghidra.start(install_dir=install_dir)
        return

    launcher = launcher_cls(verbose=False, install_dir=install_dir)
    if not hasattr(launcher, "start") or not hasattr(launcher, "uninstall_plugin"):
        pyghidra.start(install_dir=install_dir)
        return

    _install_headless_pre_launch_hook(launcher)
    launcher.start()
