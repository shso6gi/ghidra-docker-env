import os
from pathlib import Path

from scripts.function_tracer_pcode.config.settings import (
    RuntimeEnvironment,
    apply_runtime_environment,
    discover_runtime_environment,
)


def _touch(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.touch()


def test_discover_runtime_environment_prefers_repo_local_runtime_assets(tmp_path):
    ghidra_root = tmp_path / ".local-ghidra"
    _touch(ghidra_root / "ghidraRun")
    (ghidra_root / "support").mkdir(parents=True)

    java_home = tmp_path / ".local-jdk"
    _touch(java_home / "bin" / "java")

    runtime_env = discover_runtime_environment(repo_root=tmp_path, environ={})

    assert runtime_env == RuntimeEnvironment(
        ghidra_install_dir=str(ghidra_root),
        java_home=str(java_home),
    )


def test_discover_runtime_environment_uses_nested_extracted_ghidra_when_needed(tmp_path):
    extracted_root = tmp_path / ".local-ghidra-extract" / "ghidra_12.0.1_PUBLIC"
    _touch(extracted_root / "ghidraRun")
    (extracted_root / "support").mkdir(parents=True)

    runtime_env = discover_runtime_environment(repo_root=tmp_path, environ={})

    assert runtime_env.ghidra_install_dir == str(extracted_root)
    if runtime_env.java_home is not None:
        java_home = Path(runtime_env.java_home)
        assert (java_home / "bin" / "java").exists() or (java_home / "bin" / "java.exe").exists()


def test_discover_runtime_environment_respects_explicit_environment_overrides(tmp_path):
    runtime_env = discover_runtime_environment(
        repo_root=tmp_path,
        environ={
            "GHIDRA_INSTALL_DIR": "/custom/ghidra",
            "JAVA_HOME": "/custom/java",
        },
    )

    assert runtime_env == RuntimeEnvironment(
        ghidra_install_dir="/custom/ghidra",
        java_home="/custom/java",
    )


def test_apply_runtime_environment_backfills_missing_vars_without_overwriting():
    environ = {"JAVA_HOME": "/explicit/java", "PATH": "/usr/bin"}
    runtime_env = RuntimeEnvironment(
        ghidra_install_dir="/detected/ghidra",
        java_home="/detected/java",
    )

    applied = apply_runtime_environment(runtime_env=runtime_env, environ=environ)

    assert applied == runtime_env
    assert environ["GHIDRA_INSTALL_DIR"] == "/detected/ghidra"
    assert environ["JAVA_HOME"] == "/explicit/java"
    assert environ["JAVA_HOME_OVERRIDE"] == "/detected/java"
    assert environ["PATH"].split(os.pathsep)[0] == "/detected/java/bin"
