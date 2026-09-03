# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

A validation workspace for a Ghidra/PyGhidra-based **semantic equivalence checker** for compiled C functions. The Python package `scripts/function_tracer_pcode/` decompiles a function from two binaries (different arch/compiler/optimization), lifts the return semantics to an expression model, and asks SMT solvers (z3 primarily) whether the two are equivalent. Three top-level bash scripts drive large parallel "matrix" runs over the EqBench benchmark (`targets/EqBench/`, git-ignored); `paper/` holds a Japanese LaTeX manuscript about the work (it has its own `paper/AGENTS.md` rules — follow them when editing anything under `paper/`).

`main` is the only long-lived branch: start work with `git switch -c <topic> main` from the latest `main` and merge back.

## Environment and commands

The intended runtime is the container from `Dockerfile` via `docker-compose.yml` (Ghidra at `/opt/ghidra`, Temurin JDK 21, deps from `requirements-test.txt`, `z3` CLI, GNU `time`). It runs as the host uid/gid from `.env` (`DOCKER_UID`/`DOCKER_GID`, git-ignored) so bind-mount outputs stay user-owned; rebuild (`docker compose build`) whenever `Dockerfile` or `requirements-test.txt` changes. Prefix commands with `docker compose run --rm ghidra-dev`. The bare host usually has **no** `pytest`/`z3`/`pyghidra`; to run on the host instead, create the venv first:

```bash
bash scripts/setup_host_pyghidra_venv.sh     # creates .venv-pyghidra (+ .venv symlink)
```

Run scripts prefer `.venv-pyghidra/bin/python` when it exists, else `python3`; override with `PYTHON_BIN=...`. Ghidra/Java are discovered via `GHIDRA_INSTALL_DIR`/`JAVA_HOME` or repo-local ignored dirs (`.local-ghidra-extract/ghidra_*`, `.local-jdk`) — see `scripts/function_tracer_pcode/config/settings.py`.

Always run Python from the **repo root** with `-B` and the `scripts.function_tracer_pcode...` module path (the `pyproject.toml` under the package is for distribution; repository callers use the `scripts.` prefix and `tests/conftest.py` inserts the repo root on `sys.path`).

```bash
# Unit tests (pure Python; no Ghidra needed). ~170 files under tests/unit.
python3 -B -m pytest scripts/function_tracer_pcode/tests/unit -q
# Single file / single test
python3 -B -m pytest scripts/function_tracer_pcode/tests/unit/test_validation_result_summary.py -q
python3 -B -m pytest scripts/function_tracer_pcode/tests/unit/test_bounded_refinement.py -q -k <name>
# The README's smoke set (run before long reruns)
python3 -B -m pytest \
  scripts/function_tracer_pcode/tests/unit/test_validation_result_summary.py \
  scripts/function_tracer_pcode/tests/unit/test_sat_decisiveness_*.py -q

# One pairwise equivalence check (needs PyGhidra + Ghidra; binaries are built by eqbench_run_all_32jobs.sh)
python3 -B -m scripts.function_tracer_pcode.cli.main \
  --equiv targets/EqBench/benchmarks/REVE/barthe2big/Eq/source/new-arm64-clang-O0 \
          targets/EqBench/benchmarks/REVE/barthe2big/Eq/source/new-mips64-clang-O1 \
  -f f --emit-result-json -d
# Other useful flags: --binary-ids A B, --equiv-timeout, --timeout (decompile), --pairwise-timeout[-hard],
# --strategy, --list-functions, --assume-fp-non-nan, --no-retry-phases

# Shell script syntax check before touching a runner
bash -n eqbench_run_all_32jobs.sh neqbench_run_all_32jobs.sh rerun_eqbench_errors.sh

# Same, inside the container
docker compose run --rm ghidra-dev python3 -B -m pytest scripts/function_tracer_pcode/tests/unit -q
```

The suite is pure Python except one opt-in smoke test (`RUN_PYGHIDRA_REGRESSIONS=1`, in `test_cli_equivalence_import_fallback.py`) that needs a real EqBench binary; everything else uses the mocks in `tests/conftest.py` (`MockProgram`, `create_mock_analysis`, `create_mock_result`) and golden cases from `tests/fixtures/cases.yml`. Note that running the checker outside the runner's supervisor/execution-identity harness yields `ERROR` from the v2 authority layer by design — real-binary tests must go through that harness.

### EqBench matrix runs

- `eqbench_run_all_32jobs.sh` — compiles every EqBench `Eq/newV.c`/`new.c` via `scripts/eqbench/compile_all_arm_mips.sh` (arm64/mips64 × gcc/clang × O0–O3), then runs the pairwise **Eq** matrix per function. `neqbench_run_all_32jobs.sh` — **Neq** same-ISA closure (8×8 ARM64 + 8×8 MIPS64 pairs per function). Both are driven entirely by env vars (`OUTPUT_BASE_DIR`, `PARALLEL_JOBS`, `EQBENCH_SAMPLE_FILTER`, `EQBENCH_PAIR_FILTER`, `EQBENCH_RUN_SCOPE=REPRESENTATIVE|FULL_EQBENCH`, `EQBENCH_BUILD_POLICY=REUSE_OR_COMPILE|PREBUILT_ONLY|FRESH_ONLY`, `SKIP_COMPLETED_RESULTS`, `ERROR_ONLY_RERUN`, `EQBENCH_RERUN_MANIFEST`, `DRY_RUN=1`, `EQBENCH_DEBUG=1`, timeouts). Outputs go to `logs/EqBench/...` (git-ignored, currently ~24 GB of history — don't delete without asking).
- `rerun_eqbench_errors.sh` — builds `logs/EqBench/error_rerun_manifest.tsv` via `scripts/eqbench/error_rerun_manifest.py` and re-runs only ERROR pairs through the two runners above.
- Both runners `source scripts/validation_matrix_common.sh` (before/after snapshotting of `OUTPUT_BASE_DIR`, log classification, resume policy) and require bash ≥ 4.3 (`wait -n`).
- Per-pair execution is wrapped by `equivalence.v2.process_supervisor_command`, which signs receipts with per-run worker/supervisor keys under `tmp/`; a pair's final status comes from `equivalence.v2.pair_status_authority` / `canonical_result`, never from grepping the log. Summaries come from `validation.result_summary`.

## Architecture (scripts/function_tracer_pcode)

Pipeline for one function pair (`docs/equivalence_flow_diagrams.md` has mermaid diagrams):

1. **`cli/`** — `cli.main` dispatches to `runtime/pyghidra.py` (host) or `runtime/ghidra.py` (in-Ghidra script); `commands/equivalence.py` opens both programs and calls the checker.
2. **`analysis/`** — `analyzer.py` (`ReturnAnalyzer`) drives Ghidra decompilation and P-code tracing (`tracer.py`, `session.py`, `decompilation_broker.py`) into a `FunctionReturnAnalysis`: per-return-site `ReturnInfo` with path `Condition`s and an `Expression`. Sub-areas: `condition/` (simplification + SMT oracle), `recurrence/` (loop/recursion summaries), `signedness/`, `effect_*` (memory/call side effects), `analyzer_services/` and `effect_services/` (split service modules, numbered `_1`/`_2` when a module was sliced for size).
3. **`model/`** — the expression AST (`Expression`, `ExpressionType`), conditions, signatures, `render_smt.py`/`render_python.py`.
4. **`transform/`** — rewrite engine and rules (e.g. `magic_division.py` for compiler magic-number division/modulo) applied before comparison.
5. **`equivalence/`** — `checker.py` + `workflow.py` run a **phase plan** (`phases/handler.py`: `P0_BASE → P1_SIGNEDNESS → P2_PATTERN_INT`, plus off-path `P4A/P4B` MIPS64 ABI handling and `P4C` return-type fix via `typing/fixer.py`). Each phase runs a stage plan of **strategies** (`strategies/`): `PairwiseStrategy` (per-return-site obligations, `obligations/` worklist, `pairwise_services/`, `proof_gates/`) falling back to `MonolithicStrategy` on UNKNOWN/TIMEOUT. `normalize/` holds fact-based normalization; `formula/` builds solver formulas; `counterexample.py` validates SAT models.
6. **`smt/`** — solver interface and `parallel.py` racing z3/cvc5/yices2/boolector backends.
7. **`equivalence/v2/`** — "UNKNOWN Taxonomy v2": the **authority layer**. `contracts.py` defines the five-value `Outcome` (`EQUIVALENT | NOT_EQ | UNKNOWN | TIMEOUT | ERROR`), exit codes, and batch-resume dispositions; `phase8_cutover.py` projects a verified `DecisionReceipt` onto legacy fields. Consumers must read `final_outcome`/the receipt — solver rows and `is_equivalent` are never final authority. This package deliberately has no re-export surface: import the exact submodule. `registry.py` is the canonical reason-ID registry for UNKNOWN reasons.
8. **`validation/`** — summary/receipt modules used by the runners: `result_summary` (log aggregation, EQ/NOT_EQ/UNKNOWN census), `execution_identity` / `execution_receipt` / `eqbench_build_receipt` (signed run identity), `process_authority_cleanup`, `run_health_summary`, `unknown_reason_summary`, `root_blocker_summary` (used by `obligations/shadow.py`), and `phase7_producer_manifest` (builds the producer-site manifest that `phase7_runtime` consumes).

## Project rules that matter

- **Soundness rule** (from `docs/implementation-plan.md`): never reduce UNKNOWN by weakening an equivalence or disequivalence proof gate. A false EQUIVALENT is the worst failure; prefer UNKNOWN with a registered reason.
- `artifacts/unknown_taxonomy_v2/phase7/producer-sites.json` is the only tracked artifact; `phase8_cutover.py` reads it at runtime and `test_unknown_taxonomy_v2_phase7_producer_manifest.py` binds it to the current source, so regenerate it (`python3 -B -m scripts.function_tracer_pcode.validation.phase7_producer_manifest`) rather than hand-editing when producer sites change.
- Don't commit generated outputs: `logs/`, `tmp/`, `output/`, `.venv*`, `.local-*`, `targets/EqBench/` (all git-ignored). EqBench binaries are rebuilt by the runner.
- `docs/implementation-progress.md` and `docs/review-response-log.md` are the phase-status ledgers for the v2 taxonomy work; update them when completing a phase slice, not for ordinary fixes.
- Code comments and docstrings are frequently Japanese; match the surrounding language in the file you edit.
