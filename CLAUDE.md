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

Layered packages; imports point **downward only** (`core` at the bottom) and every import is absolute (`from scripts.function_tracer_pcode.<layer>... import`). Package `__init__` files re-export lazily (PEP 562), so importing one submodule never drags in a whole layer and cannot create cycles — keep it that way. `docs/equivalence_flow_diagrams.md` has mermaid diagrams of the pipeline.

| Layer | Contents |
|---|---|
| `core/` | Expression AST (`Expression`, `ExpressionType`), conditions, storage, signatures, `runtime_refs`, `render_smt`/`render_python` |
| `smt/` | Solver interface, `parallel.py` racing z3/cvc5/yices2/boolector |
| `config/` | Runtime discovery of Ghidra/Java, tunables |
| `ghidra/` | Ghidra/PyGhidra boundary: `decompilation_broker` (single production decompile entry), `pyghidra_runtime` (host mode), `ghidra_runtime` (in-Ghidra script mode), `pyghidra_support` |
| `analysis/` | P-code → return semantics. `tracer`, `phi_resolver`, `switch`, `memory_resolver`, `bounded_refinement`; `returns/` = `ReturnAnalyzer` (`analyzer.py`) + its service modules; `effects/` = memory/call side-effect models + services (`summary.py` facade); `recurrence/` = loop/recursion summaries (`summarizer.py` host); `condition/`, `signedness/` |
| `semantics/` | Expression meaning: `normalize/`, `semantic_width`, `param_semantics`, `typing/` (type-fix retries), `transform/` (expander + rewrite rules, e.g. magic-number division) |
| `proof/` | Building and discharging proofs: `formula/` (SMT formula builder), `obligations/` (worklist, proof cache, guard overlap, pair disposition), `call_effect/`, `return_width/`, `monolithic_authority`, `strategies/` (`CheckStrategy` base → `PairwiseStrategy` (`pairwise_services/`) with `MonolithicStrategy` fallback; `proof_gates/`) |
| `authority/` | Formerly `equivalence/v2`. Sealed contracts (`contracts.py`: five-value `Outcome`, exit codes; `registry.py` reason IDs), `lifecycle/` (hash-chained event `stream`, `reducer`, `execution_authority`, `production_signals`), `decision/` (`decision`, `canonical_result`, `pair_status_authority`, `production_cutover`), `process/` (OS-process `supervisor`, `worker_runtime`, `census`, brokered decompilation), `domains/` (per-domain proof authorities: sat_safety, call_effect, loop_recurrence, abi_width_readonly, return_outcome), `sites/` (producer-site activation/runtime). Consumers must read `final_outcome` / the `DecisionReceipt`; solver rows and `is_equivalent` are never final authority |
| `checker/` | Orchestration: `checker.py` + `workflow.py` run the phase plan (`phases/handler.py`: `P0_BASE → P1_SIGNEDNESS → P2_PATTERN_INT`, MIPS64 `arch/`), `result`, `unknown_reason` (typed UNKNOWN schema), `debug_trace`, `attempts`, `reanalysis` |
| `reporting/` | What the runners consume: `result_summary` (log aggregation / census), `execution_identity` / `execution_receipt` / `eqbench_build_receipt`, `process_authority_cleanup`, `phase7_producer_manifest`, `formatter` |
| `cli/` | `cli.main` → `ghidra.pyghidra_runtime` or `ghidra.ghidra_runtime`; `commands/equivalence.py` opens both programs and drives the checker |

Service-function convention: `ReturnAnalyzer`, `StructuralRecurrenceSummarizer`, `CheckStrategy`, `PairwiseStrategy` and the `effects.summary` facade get their methods from module-level `_impl_<name>(self, ...)` functions in topical sibling modules (e.g. `analysis/returns/parameters.py`, `analysis/recurrence/varnode_algebra.py`, `proof/strategies/pairwise_services/method_b_closure.py`), bound explicitly in the host class body (`name = _svc_module._impl_name`). To add a method: write `_impl_<name>` in the module whose topic fits and add one binding line (plus an entry in `implementations()` for `proof_gates`/`pairwise_services`, whose table is snapshotted to seal the producer-proof bundle). Each family's `_shared.py` is its import hub; `_api.py` late-binds a few facade names so tests can monkeypatch them.

Large classes are composed from mixins living next to the host: `EquivalenceChecker(AbiRetryMixin, PreflightGateMixin, RootCauseMixin, RecoveryProofMixin, RecurrenceStageMixin)` in `checker/`, `PcodeTracer(CallRecoveryMixin, ParameterStorageMixin, AddressRefMixin)` in `analysis/`, `ExpressionExpander(...)` in `semantics/transform/`, `MonolithicStrategy(...)` in `proof/strategies/`, `ConditionSimplifier(...)` in `analysis/condition/`; helpers shared by a host and its mixins live in `<host>_support.py` (mixins never import their host). `core/runtime_refs/` and `core/render_smt/` are packages whose `__init__` re-exports everything, so `from ...core.runtime_refs import LoopSummaryRef` keeps working; sibling modules import each other at the module tail (or lazily) to stay cycle-free. When a test monkeypatches a module-level name, patch the module where the method that reads it now lives.

Known remaining upward dependencies to work off (tracked as tech debt, not bugs): `proof → authority` (producers emit authority signals), `proof → checker` / `proof → reporting`, `authority → checker`, `ghidra → authority`, `ghidra → cli` (the runtime entry modules dispatch to `cli.commands`), `core → analysis` (`core/analysis.py` lazily imports condition simplifier / effect summary), `analysis → semantics` / `analysis → proof` / `analysis → authority`. The exact importing modules are pinned as a baseline in `tests/unit/test_import_layers.py`; that test fails on any new upward edge (add no baseline entries — move the code to the owning layer) and on stale entries (remove them when debt is paid).

## Project rules that matter

- **Ask, don't assume.** When something is unclear (an ambiguous requirement, a design choice with material consequences, an Issue that is insufficient or contradictory), do not state a guess as fact: present the options and confirm with the user before proceeding. Facts that can be established from the code or by running it should be established that way first.
- **General, extensible fixes over ad-hoc patches.** The analysis program is meant to grow: fix the class of problem in the layer that owns it (e.g. a memory-resolution rule, a proof gate, a registered UNKNOWN reason), not the one benchmark case that exposed it. Avoid special-casing sample names, string matching on rendered output, or hard-coded constants; prefer a mechanism that other producers/consumers can reuse.
- **Soundness rule** (from `docs/implementation-plan.md`): never reduce UNKNOWN by weakening an equivalence or disequivalence proof gate. A false EQUIVALENT is the worst failure; prefer UNKNOWN with a registered reason.
- `artifacts/unknown_taxonomy_v2/phase7/producer-sites.json` is the only tracked artifact; `phase8_cutover.py` reads it at runtime and `test_unknown_taxonomy_v2_phase7_producer_manifest.py` binds it to the current source, so regenerate it (`python3 -B -m scripts.function_tracer_pcode.reporting.phase7_producer_manifest`) rather than hand-editing when producer sites change.
- Don't commit generated outputs: `logs/`, `tmp/`, `output/`, `.venv*`, `.local-*`, `targets/EqBench/` (all git-ignored). EqBench binaries are rebuilt by the runner.
- `docs/implementation-progress.md` and `docs/review-response-log.md` are the phase-status ledgers for the v2 taxonomy work; update them when completing a phase slice, not for ordinary fixes.
- Code comments and docstrings are frequently Japanese; match the surrounding language in the file you edit.
