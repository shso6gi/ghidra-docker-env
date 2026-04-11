# -*- coding: utf-8 -*-
"""Typed runtime accessors for the optional pyghidra dependency."""

from __future__ import annotations

from importlib import import_module
from pathlib import Path
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
