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

The analysis target is EqBench (`targets/EqBench/`, git-ignored; clone or copy
the benchmark tree there). `eqbench_run_all_32jobs.sh` compiles every
`Eq/newV.c` / `Eq/new.c` sample into `Eq/source/` with
`scripts/eqbench/compile_all_arm_mips.sh` (arm64/mips64 x gcc/clang x O0-O3)
before running the matrix, so no manual build step is needed. Set
`EQBENCH_BUILD_POLICY=PREBUILT_ONLY` to reuse existing binaries only.

## Generated outputs

These paths are intentionally not git-managed:

- `logs/`
- `tmp/`
- `output/`
- `.venv/`, `.venv-pyghidra/`
- `.local-ghidra/`, `.local-ghidra-extract/`, `.local-jdk/`
- `targets/EqBench/`

In the current host setup, keep `.venv`, `.venv-pyghidra`,
`.local-ghidra-extract/`, and `.local-jdk/` if you want Codex or other tools to
run PyGhidra outside the container. `.local-ghidra/` is not used unless it
contains a valid `ghidraRun`; it is safe to remove when only partial license or
support files are present.

Selected validation evidence under `artifacts/` (UNKNOWN taxonomy v2 receipts,
refactor contracts, audits) is git-managed because `validation/*.py` and unit
tests depend on it.

To inspect ignored local outputs without deleting them:

```bash
bash scripts/clean_local_generated.sh
```

To remove generated logs/tmp after they are no longer needed and remove the
unused `.local-ghidra/` cache if present:

```bash
CLEAN_LOCAL_GENERATED_CONFIRM=1 bash scripts/clean_local_generated.sh
```

Required host runtime caches are preserved by default. To remove them too:

```bash
CLEAN_LOCAL_GENERATED_CONFIRM=1 CLEAN_REQUIRED_HOST_RUNTIME=1 bash scripts/clean_local_generated.sh
```

## EqBench runs

Before a long run, require a clean tree and a passing unit suite:

```bash
git status --short
python3 -B -m pytest scripts/function_tracer_pcode/tests/unit -q
bash -n eqbench_run_all_32jobs.sh neqbench_run_all_32jobs.sh
```

Full Eq matrix (results under `logs/EqBench/all_eq_matrix_current`):

```bash
./eqbench_run_all_32jobs.sh
# representative subset / single sample
EQBENCH_SAMPLE_FILTER='REVE/barthe2big' ./eqbench_run_all_32jobs.sh
# validate configuration without running pairs
DRY_RUN=1 ./eqbench_run_all_32jobs.sh
```

Neq same-ISA closure (results under `logs/EqBench/all_neq_same_isa_closure_current`):

```bash
./neqbench_run_all_32jobs.sh
```

Re-run only the pairs that ended in ERROR in both trees:

```bash
./rerun_eqbench_errors.sh
```

All runners are configured through environment variables (`PARALLEL_JOBS`,
`OUTPUT_BASE_DIR`, `EQBENCH_RUN_SCOPE`, `EQBENCH_BUILD_POLICY`,
`SKIP_COMPLETED_RESULTS`, `ERROR_ONLY_RERUN`, timeouts); see the header of each
script for the full list and defaults.

## Branching

`main` is the integration branch. Start every piece of work from the latest
`main` (`git switch -c <topic> main`) and merge back when done; do not keep
long-lived side branches.
