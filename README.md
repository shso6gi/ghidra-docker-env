# ghidra-docker-env

Validation workspace for Ghidra/PyGhidra based semantic equivalence checks.

## Container workflow

All analysis runs inside the image defined by `Dockerfile`, driven through
`docker-compose.yml`. Use git for source, scripts, manifests, and test
definitions; do not sync local runtime caches or generated outputs.

One-time setup so files written into the bind mount stay owned by you:

```bash
printf 'DOCKER_UID=%s\nDOCKER_GID=%s\n' "$(id -u)" "$(id -g)" > .env
docker compose build
```

Rebuild the image after a `git pull` whenever `Dockerfile` or
`requirements-test.txt` changed. Then:

```bash
docker compose run --rm ghidra-dev                    # interactive shell in /workspace
docker compose run --rm ghidra-dev python3 -B -m pytest scripts/function_tracer_pcode/tests/unit -q
```

The image installs:

- Ghidra 12.0.1 under `/opt/ghidra` (zip verified by SHA-256)
- Temurin JDK 21 under `/usr/lib/jvm/temurin-21-jdk-amd64`
- clang plus the GNU arm64/mips64 cross toolchains used to build EqBench
- Python dependencies from `requirements-test.txt`, the `z3` CLI, and GNU `time`

Python package versions are pinned in `requirements-test.txt`. Apt packages,
the Adoptium repository, and the Ubuntu package index are still
time-dependent; rebuild the image from the same commit before comparing long
rerun results across machines.

## Host PyGhidra Environment

The preferred runtime is the container above. If Codex or another tool must run
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

Run everything below inside the container (`docker compose run --rm ghidra-dev <command>`
or from an interactive shell). Before a long run, require a clean tree and a
passing unit suite:

```bash
git status --short
python3 -B -m pytest scripts/function_tracer_pcode/tests/unit -q
bash -n eqbench_run_all_32jobs.sh neqbench_run_all_32jobs.sh
```

Default settings for benchmark runs on this host are `PARALLEL_JOBS=20` with
resource admission disabled (`EQBENCH_RESOURCE_ADMISSION=0`); the baseline trees
under `logs/EqBench/*_current` were produced with them. Both runners record the
effective values in `run_manifest.txt`.

Full Eq matrix (results under `logs/EqBench/all_eq_matrix_current`):

```bash
PARALLEL_JOBS=20 EQBENCH_RESOURCE_ADMISSION=0 ./eqbench_run_all_32jobs.sh
# representative subset / single sample
EQBENCH_SAMPLE_FILTER='REVE/barthe2big' ./eqbench_run_all_32jobs.sh
# validate configuration without running pairs
DRY_RUN=1 ./eqbench_run_all_32jobs.sh
```

Neq same-ISA closure (results under `logs/EqBench/all_neq_same_isa_closure_current`):

```bash
PARALLEL_JOBS=20 EQBENCH_RESOURCE_ADMISSION=0 ./neqbench_run_all_32jobs.sh
```

Re-run only the pairs that ended in ERROR in both trees:

```bash
./rerun_eqbench_errors.sh
```

All runners are configured through environment variables (`PARALLEL_JOBS`,
`OUTPUT_BASE_DIR`, `EQBENCH_RUN_SCOPE`, `EQBENCH_BUILD_POLICY`,
`SKIP_COMPLETED_RESULTS`, `ERROR_ONLY_RERUN`, timeouts); see the header of each
script for the full list and defaults.

### Measurement subset

`scripts/function_tracer_pcode/reporting/eqbench_subset.json` fixes a small
Eq + Neq subset (8 Eq sources and 10 Neq sources, one function and 8 pairs each) for comparing
checker behaviour before and after a change. `eqbench_run_subset.sh` runs it
with the settings stored in the manifest (`PARALLEL_JOBS=20`,
`EQBENCH_RESOURCE_ADMISSION=0`, `EQBENCH_BUILD_POLICY=PREBUILT_ONLY`,
`PAIR_PROCESS_TIMEOUT=240s`), running the Eq and Neq halves concurrently, and finishes in under 10 minutes:

```bash
OUTPUT_BASE_DIR=logs/EqBench/subset_before ./eqbench_run_subset.sh   # e.g. on main
OUTPUT_BASE_DIR=logs/EqBench/subset_after  ./eqbench_run_subset.sh   # on the topic branch
# SUBSET_SCOPE=eq|neq runs one half only; env overrides (PARALLEL_JOBS, ...) win over the manifest
```

Each run writes `eq/` and `neq/` result trees plus `subset_manifest.txt`
(manifest digest, settings, elapsed seconds). Note that the subset uses a
240 s pair timeout instead of the 600 s of full runs, so TIMEOUT counts are not
comparable with the full trees.

Compare two runs with the outcome transition table (rows: before, columns:
after; `--fail-on-change` exits 2 on any difference, which is how determinism
is checked by running the subset twice):

```bash
python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
    --before logs/EqBench/subset_before/eq --after logs/EqBench/subset_after/eq --changed-only
python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
    --before logs/EqBench/subset_before/neq --after logs/EqBench/subset_after/neq --changed-only --json neq_transition.json
```

Check soundness against the benchmark labels only (an `Eq` sample must never be
`NOT_EQ`, a `Neq` sample must never be `EQUIVALENT`; exit 1 on any violation,
exit 2 when no pair status was found):

```bash
python3 -m scripts.function_tracer_pcode.reporting.soundness_gate \
    logs/EqBench/subset_after/eq logs/EqBench/subset_after/neq
```

The gate currently fails on `logs/EqBench/all_neq_same_isa_closure_current`
(242 `EQUIVALENT` pairs in Neq samples). The manifest's `observed_baseline`
section records what the checker produced at the recorded commit; it is
explicitly *not* ground truth — an EQUIVALENT/NOT_EQ there may be an accident
of an implementation defect — and must only be used to explain transitions.

## Branching

`main` is the integration branch. Start every piece of work from the latest
`main` (`git switch -c <topic> main`) and merge back when done; do not keep
long-lived side branches.
