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

The checker's own input is exactly the two binaries passed to `--equiv`. It
never reads files that happen to sit next to them: the `newV.c` / `new.c`
sources copied into `Eq/source/` alongside the compiled binaries are inputs to
the benchmark evaluation oracle (`scripts/eqbench/function_diff_manifest.py`,
`reporting/benchmark_validation_gate.py`), never to the semantic judgement,
its provenance, or the signed execution identity.

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

Default settings for benchmark runs on this host are `PARALLEL_JOBS=32` with
resource admission disabled (`EQBENCH_RESOURCE_ADMISSION=0`); the baseline trees
under `logs/EqBench/*_current` were produced with them. Both runners record the
effective values in `run_manifest.txt`.
Pair jobs are scheduled across functions by `scripts/eqbench/pair_scheduler.sh`,
so `PARALLEL_JOBS` pairs stay in flight even when one function contributes fewer
pairs; each function's `results_summary.txt` is still written as soon as its last
pair finishes, and the run prints the peak concurrency at the end.

Full Eq matrix (results under `logs/EqBench/all_eq_matrix_current`):

```bash
PARALLEL_JOBS=32 EQBENCH_RESOURCE_ADMISSION=0 ./eqbench_run_all_32jobs.sh
# representative subset / single sample
EQBENCH_SAMPLE_FILTER='REVE/barthe2big' ./eqbench_run_all_32jobs.sh
# validate configuration without running pairs
DRY_RUN=1 ./eqbench_run_all_32jobs.sh
```

Neq same-ISA closure (results under `logs/EqBench/all_neq_same_isa_closure_current`):

```bash
PARALLEL_JOBS=32 EQBENCH_RESOURCE_ADMISSION=0 ./neqbench_run_all_32jobs.sh
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
with the settings stored in the manifest (`PARALLEL_JOBS=32`,
`EQBENCH_RESOURCE_ADMISSION=0`, `EQBENCH_BUILD_POLICY=PREBUILT_ONLY`,
`PAIR_PROCESS_TIMEOUT=240s`), running the Eq half and then the Neq half (each runner
already fills `PARALLEL_JOBS` slots on its own):

```bash
OUTPUT_BASE_DIR=logs/EqBench/subset_before ./eqbench_run_subset.sh   # e.g. on main
SUBSET_BEFORE=logs/EqBench/subset_before SUBSET_ISSUE=123 SUBSET_PR=151 \
    OUTPUT_BASE_DIR=logs/EqBench/subset_after ./eqbench_run_subset.sh   # on the topic branch
# SUBSET_SCOPE=eq|neq runs one half only; env overrides (PARALLEL_JOBS, ...) win over the manifest
```

Each run writes `eq/` and `neq/` result trees plus `subset_manifest.txt`
(manifest digest, settings, elapsed seconds, and the run's own provenance:
`git_commit`, `git_dirty`, `git_dirty_files_digest`, `start_time_utc`,
`end_time_utc`, `hostname`). `SUBSET_BEFORE` names the run this one is compared
against; it is checked before the first pair starts, and the transition report
of each half plus this run's soundness gate are then saved next to the results.
Note that the subset uses a 240 s pair timeout instead of the 600 s of full
runs, so TIMEOUT counts are not comparable with the full trees.

Compare two runs with the outcome transition table (rows: before, columns:
after; `--fail-on-change` exits 2 on any difference, which is how determinism
is checked by running the subset twice):

```bash
python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
    --before logs/EqBench/subset_before/eq --after logs/EqBench/subset_after/eq --changed-only
python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
    --before logs/EqBench/subset_before/neq --after logs/EqBench/subset_after/neq --changed-only --json neq_transition.json
```

Four opt-in sections add the rest of the comparison. They are opt-in so the
command above keeps printing and serializing exactly what it did before, and
none of them can move `--fail-on-change` (which still means, and only means,
"an unconditional outcome changed or a pair is missing on one side"):

```bash
python3 -m scripts.function_tracer_pcode.reporting.outcome_transition \
    --before logs/EqBench/subset_before/eq --after logs/EqBench/subset_after/eq \
    --axes --reason-sets --manifest --runtime-metrics --changed-only
```

- `--reason-sets` compares the **final UNKNOWN reason-id set** of every pair
  (pair identity, canonical outcome and reason ids only — never a per-run
  digest). A pair whose result payload cannot be read on either side, or that
  exists on one side only, is `incomparable` and is counted separately: it is
  never counted as a match. This replaces the `compare_reason_sets.py` that
  used to be copied into each run directory by hand.
- `--manifest` checks each tree against its own
  `matrix-publication-manifest.json` (`expected_pair_status_paths` versus the
  pair statuses actually on disk). It is fail-closed: a missing or
  unexpectedly-schema'd manifest gives `unknown`, and a missing pair, an
  unexpected pair, or a pair the run only reused from an earlier run
  (`verified_skipped_pair_status_paths`) gives `partial`. Only a tree that
  expected some pairs and executed all of them is `complete`.
- `--runtime-metrics` reads `.runtime-metrics/<pair>.runtime.json` for the
  wall-clock delta. It is informational only — it never changes an exit code,
  it always states how much of each tree it could see, and a pair without a
  receipt is never read as zero seconds. (The Neq runner does not write these
  receipts, so its coverage is reported as incomplete rather than as "no
  change".)
- `--axes` adds the three axes below.

#### The three axes (EPIC #130) — do not fold them into one verdict

"the outcome changed", "the outcome is right" and "the gate passed" are three
different claims, so they are reported as three independent groups of counters:

| axis | values | source |
|---|---|---|
| **A. correctness** | `confirmed_consistent` / `confirmed_contradicted` / `unconfirmed` / `not_applicable` | The `Eq` label (one source on both sides) is its own ground truth. A `Neq` decision needs `semantic_ground_truth` from the tree's own `function_diff_manifest.json`; `source_relation` / `source_impact` are **not** a substitute for it. Anything else is `unconfirmed`; a non-decisive outcome is `not_applicable`. |
| **B. transition** | `capability_improvement` / `classification_change` / `regression` / `other` | A new decision is an improvement **only when axis A confirms it**. A new decision nothing can confirm is `other` with the note `decided_but_unconfirmed`, counted on its own. A decision a ground truth contradicts, and any loss of a decision, is a `regression`. |
| **C. gate** | `violation` / `suspicious` / `ok` / `not_applicable` | `benchmark_validation_gate`'s own classification, grouped. A gate `ok` means "the gate found nothing to complain about", never "this decision is correct". |

Most `Neq` `NOT_EQ` results sit in axis A's `unconfirmed` bucket, because their
reviewed ground truth is `UNKNOWN`. They must never be counted as correct
decisions or as improvements. EPIC #130's fourth category,
*performance improvement*, is not an outcome transition: it needs per-pair wall
clock and is therefore reported by `--runtime-metrics` only, so that a run
without runtime receipts cannot silently report "no performance change".

Axis B can only see a reason-set change when `--reason-sets` is also on; the
report says so explicitly rather than letting a zero be read as "no reason
changed".

### Verification ledger

`reporting/verification_ledger.py` keeps one JSON line per verification run in
`logs/EqBench/verification_ledger.jsonl` (git-ignored), replacing the
hand-written `NOTES.md` that used to record which commit a run was made on,
what it was compared against and how far it got. `eqbench_run_subset.sh` calls
`record` itself at the end of a run.

```bash
python3 -m scripts.function_tracer_pcode.reporting.verification_ledger \
    record --run-dir logs/EqBench/subset_after --requested-scope subset \
    --before logs/EqBench/subset_before --issue 123 --pr 151
python3 -m scripts.function_tracer_pcode.reporting.verification_ledger list
```

**The ledger is a measurement aid, never an authority.** It only reads
artifacts other tools already wrote (pair statuses, the runner manifests, the
publication manifests, the gates); it cannot change a pair's outcome or a
receipt. The `record` call happens after every pair has been judged and after
the soundness and transition artifacts exist, and a failure to record is a
diagnostic — it leaves `ledger_record_status` in `subset_manifest.txt` and
never becomes the runner's exit status.

Three distinctions the schema exists to keep apart:

- **`requested_scope` vs `completed_scope`.** "A run exists" and "the range
  that was asked for was actually verified" are different facts.
  `requested_scope` (`subset` / `focused` / `full_eq` / `full_neq`) is supplied
  by the caller and never guessed from the results; `completed_scope`
  (`complete` / `partial` / `unknown`) comes from the `--manifest` rules above,
  applied to every tree of the run and folded fail-closed (any `unknown` wins,
  then any `partial`). A run that expected no pairs is `unknown`, not
  `complete`. There is deliberately **no single `full_evaluation` boolean**.
- **`coverage`.** The counted evidence behind `completed_scope`:
  `pairs_expected`, `pairs_with_status`, `pairs_missing`, `pairs_unexpected`,
  `pairs_verified_skipped` (reused from an earlier run, not executed here) and
  `pairs_incomparable` (a status exists but no readable result payload, so the
  reason set cannot be checked). A pair nobody looked at is never counted as
  one that was checked.
- **`code_matches_head` / `stale_code`.** Computed by `list` against the
  *current* HEAD and never stored, because a stored answer would rot as HEAD
  moves. `yes` requires a recorded commit equal to the current HEAD, a run that
  was not dirty, and a working tree whose git state can be read right now;
  a different commit or a dirty run is `no`, and missing or unreadable
  provenance is `unknown`. Anything that is not `yes` is marked `stale_code`,
  which means **"this is not evidence about the code at HEAD"** — not "this run
  was invalid". A past run remains a perfectly good record of the commit it was
  made on.

`list` names the last run recorded for each full scope, then every run recorded
after it, and ends with an explicit answer to "has everything been evaluated at
the current HEAD?". A ledger holding only subset rows can never print
"full verified": **subset verification is not full verification**, and a subset
row says nothing about the pairs outside the subset.

The three axes are stored as three separate groups of counters, exactly as
`outcome_transition --axes` computes them, and are never folded into one
`PASS`. Rows also carry the run's provenance, timings, settings, outcome
counts, the persisted gate verdicts (a gate whose artifact is absent is
`unknown`, never `PASS`) and an `unresolved_variance` list to fill in by hand
when an indicator moved and a rerun did not settle whether it was the code or
run-to-run noise.

Check soundness against the benchmark labels only (an `Eq` sample must never be
`NOT_EQ`, a `Neq` sample must never be `EQUIVALENT`; exit 1 on any violation,
exit 2 when no pair status was found):

```bash
python3 -m scripts.function_tracer_pcode.reporting.soundness_gate \
    logs/EqBench/subset_after/eq logs/EqBench/subset_after/neq
```

The label-only gate cannot tell a legitimate `EQUIVALENT` on an unchanged Neq
helper from a false one, so both runners end with the function-level
**benchmark validation gate** (`EQBENCH_BENCHMARK_GATE=0` disables it;
`EQBENCH_GROUND_TRUTH_FILE` points it at another reviewed annotation file, e.g.
an empty one for a synthetic benchmark root; a missing file fails the gate). It
builds `function_diff_manifest.json` from the actual `old.c`/`new.c` of the
benchmark tree (`scripts/eqbench/function_diff_manifest.py`: per function
`source_relation`, `source_impact`, `semantic_ground_truth`; `C-Desc.json` is
only audited, never trusted) and classifies every canonical pair outcome:

- hard violations (runner exits 1): `Eq` → `NOT_EQ`; `Neq` function annotated
  `CONFIRMED_NOT_EQ` in `scripts/eqbench/neq_ground_truth.tsv` → `EQUIVALENT`;
  annotated `CONFIRMED_EQ` → `NOT_EQ`; `Neq` `EQUIVALENT` the manifest cannot
  classify; an annotation that matches no function (the manifest build, and
  so the runner, fails closed);
- suspicious (counted only, `EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS=1` to
  fail): `EQUIVALENT` on a source-impacted Neq function whose ground truth is
  still `UNKNOWN`, `NOT_EQ` on a source-identical Neq function.

A source change is never turned into a semantic verdict automatically; the
checker never reads the manifest or the annotation file. The gate writes
`benchmark_validation_gate.{json,txt}`, extends `run_health_summary.{json,txt}`
(`soundness_violations: eq_not_eq=… neq_equivalent=… neq_not_eq_on_confirmed_eq=… neq_equivalent_unmapped=…`)
and both artifacts are hashed into `validation-execution-receipt.json`. Offline:

```bash
python3 scripts/eqbench/function_diff_manifest.py \
    --benchmark-root targets/EqBench/benchmarks --output /tmp/function_diff_manifest.json
python3 -m scripts.function_tracer_pcode.reporting.benchmark_validation_gate \
    logs/EqBench/all_neq_same_isa_closure_current --manifest /tmp/function_diff_manifest.json
```

On `logs/EqBench/all_neq_same_isa_closure_current` (produced before the #13
fix) the label-only gate fails on all 242 `EQUIVALENT` pairs in Neq samples;
the benchmark validation gate fails on the 192 raytrace constructor pairs
whose reviewed ground truth is `CONFIRMED_NOT_EQ` and counts the 50
`CLEVER/UnchLoop foo` pairs as suspicious (source changed, equivalence not
confirmed at the binary level). The manifest's `observed_baseline`
section records what the checker produced at the recorded commit; it is
explicitly *not* ground truth — an EQUIVALENT/NOT_EQ there may be an accident
of an implementation defect — and must only be used to explain transitions.

## Branching

`main` is the integration branch. Start every piece of work from the latest
`main` (`git switch -c <topic> main`) and merge back when done; do not keep
long-lived side branches.
