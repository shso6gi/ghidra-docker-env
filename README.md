# ghidra-docker-env

Validation workspace for Ghidra/PyGhidra based semantic equivalence checks.

## Git-managed workflow

Use git for source, scripts, manifests, and test definitions. Do not sync local
runtime caches or generated outputs.

The primary container entrypoint is `.devcontainer/devcontainer.json`. After a
`git pull`, rebuild the Dev Container when `.devcontainer/Dockerfile` or
`requirements-test.txt` changes. Reopening an existing container is not enough
to pick up image dependency changes.

Recommended Dev Containers flow:

```bash
git pull
# VS Code: Dev Containers: Rebuild and Reopen in Container
```

Equivalent CLI flow with the Dev Containers CLI:

```bash
git pull
devcontainer up --workspace-folder .
```

`docker-compose.yml` is optional for non-VS Code runs and uses the same
Dockerfile:

```bash
git pull
docker compose build ghidra-dev
docker compose run --rm ghidra-dev bash
```

Inside the container:

```bash
python3 -B -m pytest \
  scripts/function_tracer_pcode/tests/unit/test_validation_result_summary.py \
  scripts/function_tracer_pcode/tests/unit/test_sat_decisiveness_*.py -q

VALIDATION_RUNNER_DRY_RUN=1 \
./phase2_run_function_call_pre_producer_final_result_preflight.sh
```

The devcontainer uses the same image definition. It mounts the repository at
`/workspace`.

## Runtime dependencies

The Docker image installs:

- Ghidra under `/opt/ghidra`
- Temurin JDK 21 under `/usr/lib/jvm/temurin-21-jdk-amd64`
- Python dependencies from `requirements-test.txt`
- the `z3` CLI package and Python `z3-solver`

Python package versions are pinned in `requirements-test.txt`. The Ghidra zip
download is verified by SHA-256 in the Dockerfile. Apt packages, the Adoptium
repository, and the Ubuntu package index are still time-dependent; rebuild the
image from the same commit before comparing long rerun results across machines.

## Host PyGhidra Environment

The preferred runtime is the Dev Container. If Codex or another tool must run
PyGhidra directly on the host, create a local venv on each machine instead of
copying one from another PC:

```bash
bash scripts/setup_host_pyghidra_venv.sh
```

This creates `.venv-pyghidra` and a `.venv` symlink, installs
`requirements-test.txt`, and verifies Python imports for `pyghidra` and `z3`.
Host direct PyGhidra execution also needs Ghidra and Java available through
`GHIDRA_INSTALL_DIR` / `JAVA_HOME` or repo-local ignored directories. In the
current host setup, `.local-ghidra-extract/ghidra_12.0.1_PUBLIC` and
`.local-jdk` provide those runtime paths.

Do not git-manage `.venv`, `.venv-pyghidra`, `.local-ghidra*`, or
`.local-jdk`. Delete `.venv` / `.venv-pyghidra` only when you are ready to
recreate the host venv with the setup script, or when you only use the Dev
Container.

## Target binaries

`targets/**/*.c` and the active `targets/**/compile_all.sh` scripts are tracked.
Generated target binaries are ignored and should be rebuilt in the container
when needed. `targets/cate1/loop_recursion_test/` is currently ignored because
it contains generated binaries without a tracked source file.

Example:

```bash
cd targets/cate1/function_call_test
./compile_all.sh
```

## Generated outputs

These paths are intentionally not git-managed:

- `logs/`
- `tmp/`
- `output/`
- `.venv/`, `.venv-pyghidra/`
- `.local-ghidra/`, `.local-ghidra-extract/`, `.local-jdk/`

In the current host setup, keep `.venv`, `.venv-pyghidra`,
`.local-ghidra-extract/`, and `.local-jdk/` if you want Codex or other tools to
run PyGhidra outside the container. `.local-ghidra/` is not used unless it
contains a valid `ghidraRun`; it is safe to remove when only partial license or
support files are present.

Baseline manifests and selected validation evidence under `artifacts/baselines/`
are git-managed when scripts depend on them. This repository currently keeps
some tracked `.log` and `.txt` evidence under `artifacts/`; top-level generated
`logs/` and multi-GB raw baseline logs are excluded.

To inspect ignored local outputs without deleting them:

```bash
bash scripts/clean_local_generated.sh
```

To remove generated logs/tmp/raw baseline logs after they are no longer needed
and remove the unused `.local-ghidra/` cache if present:

```bash
CLEAN_LOCAL_GENERATED_CONFIRM=1 bash scripts/clean_local_generated.sh
```

Required host runtime caches are preserved by default. To remove them too:

```bash
CLEAN_LOCAL_GENERATED_CONFIRM=1 CLEAN_REQUIRED_HOST_RUNTIME=1 bash scripts/clean_local_generated.sh
```

## Full rerun

Before a long rerun, require a clean tree:

```bash
git status --short
./.venv/bin/python -B -m pytest \
  scripts/function_tracer_pcode/tests/unit/test_validation_result_summary.py \
  scripts/function_tracer_pcode/tests/unit/test_sat_decisiveness_*.py -q
bash -n phase2_run_function_call_pre_producer_final_result_preflight.sh
```

To check only the Phase 2 producer functions that contributed to the latest
canonical-baseline gate failure, run the reduced matrix first:

```bash
./phase2_run_function_call_pre_producer_reduced_matrix.sh
```

Then run the full 20-function sequence. It enters the 20-function matrices
directly after unit tests:

```bash
./rerun_full_analysis.sh
```

For a short targeted check of Phase 2 producer reason-tuple movement, run the
preflight manually:

```bash
./phase2_run_function_call_pre_producer_final_result_preflight.sh
```
