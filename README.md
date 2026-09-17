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
the benchmark tree there). Upstream is <https://github.com/shrBadihi/EqBench>,
pinned at commit `3724fce5b287cc63165028444daf904f25b0158b` and distributed
under the MIT licence (`targets/EqBench/LICENSE.md`; a copy of the licence text
and of what the checked-in fixtures derive from it is in
`scripts/function_tracer_pcode/tests/fixtures/pcode/NOTICE.md`).
`eqbench_run_all_32jobs.sh` compiles every
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

### Recorded P-code fixtures (Issue #109)

`scripts/function_tracer_pcode/tests/fixtures/pcode/` holds recordings of what
real Ghidra returned for a pair of EqBench binaries, so the production
`check_from_binaries` path can be replayed in CI without Ghidra.

`cases.json` describes the eight-case corpus `tests/unit/test_recorded_pairs.py`
replays; `expected/` holds one regression expectation per case (and per variant
for the byte-identical pair, which is replayed with the identity fast path both
on and off from a single fast-path-**off** recording). Each replay runs in its
own process, the way production runs one pair per process, and `budget_seconds`
is applied as a real deadline: the worker's process group is killed when it
expires, so a hung replay fails fast instead of running into the job timeout.
Both that budget and the whole-corpus `corpus_budget_seconds` (1200 s, the
Issue #109 time criterion revised on 2026-09-17, measured as the **sum** of the
replay times and never as a parallel workflow's wall clock) are test-harness
failure conditions and never become a production UNKNOWN or TIMEOUT.
`ground_truth/` holds
*references* to the semantic relation, never the relation itself: the source of
truth is `scripts/eqbench/neq_ground_truth.tsv` (reviewed, with an independent
native execution witness) plus `function_diff_manifest`'s single-source rule for
Eq samples, and `scripts/eqbench/ground_truth_conditional_compatibility.json`
for whether a relation survives a conditional proof's premises. The EqBench
directory lane (`Eq` / `Neq`) is a dataset label, not a ground truth, and never
decides a soundness violation on its own. The checker reads none of these files.

Read the binaries from a **fresh writable working root**, never from the
canonical `targets/EqBench/` checkout: the runners write `Eq/source/` into
whatever root they are pointed at, so the canonical checkout stays read-only.
The recorder enforces this — it takes the working root explicitly and refuses a
binary that lies outside it, or a working root inside the canonical checkout.

```bash
W=tmp/eqbench-work/3724fce5
[[ ! -e "$W" ]] || { echo "working root exists: $W (rm -rf it first)" >&2; exit 1; }
mkdir -p "$W/benchmarks" && cp -a targets/EqBench/benchmarks/. "$W/benchmarks/"

docker compose run --rm ghidra-dev python3 -B -m scripts.function_tracer_pcode.tests.tools.record_pcode_fixture \
  --eqbench-root /workspace/$W/benchmarks \
  --left  /workspace/$W/benchmarks/bess/bessj0/Eq/source/newV-arm64-clang-O0 \
  --right /workspace/$W/benchmarks/bess/bessj0/Eq/source/newV-arm64-clang-O1 \
  --function snippet --binary-ids B1 B2 --fixture-id bessj0_snippet_B1_B2 \
  --output-dir scripts/function_tracer_pcode/tests/fixtures/pcode/bessj0_snippet_B1_B2 \
  --work-dir tmp/record-pcode
```

`binary.eqbench_relative_path` / `sha256` describe the file that was actually
read from the working root; `eqbench.upstream_url` / `commit` come from the
canonical read-only checkout. The two are separate facts and are recorded
separately.

Recording the same input twice is byte-identical (compare with
`--compare <dir-a> <dir-b>`, which only excludes the volatile
`recorded_at_utc` / `recording_dirty` header fields). The two values Ghidra
varies per import — an object's identity hash and the program's unique ID —
are recorded as surrogates that **preserve the equality and collision relation
of the observed raw values** while replacing the values themselves; the raw
numbers never enter the fixture. A legal `hashCode()` collision between two
unequal objects survives as a collision, and a recording stops outright if
Java-equal receivers report different hashes — a contract the fixture loader
re-checks with the same implementation.

Where the replays run:

| | runs | replays |
|---|---|---|
| `unit-fast` (every PR) | the ordinary suite plus the cheap corpus contracts in `tests/unit/test_recorded_corpus_contracts.py` | none -- `-m "not recorded_replay"` **deselects** them (it does not skip them) |
| `recorded-fast` (every PR, parallel with `unit-fast`) | `tests/unit/test_recorded_pairs.py` at its default `pr_gate` tier | the 7 replays `cases.json` marks `pr_gate: true` |
| `recorded-full` (push to `main`, `workflow_dispatch`, weekly) | one replay per matrix shard, then an aggregate job | all 9, `fail-fast: false` |

Both gates and the full matrix call the same `validate_replay`, so no case is
checked less anywhere; `wood` and `barthe2big` are outside the PR gate only
because they are ~92 % of the corpus wall clock. The aggregate job replays
nothing: it reads one record per shard -- written only after that replay passed
every check, so a missing record is a hard failure, never a skip -- and applies
the completeness and budget contract from
`tests/fixtures/pcode/corpus.py`, the same function the serial run uses.

```bash
# the whole corpus locally, then the same aggregate the matrix job runs
python3 -B -m pytest scripts/function_tracer_pcode/tests/unit/test_recorded_pairs.py   --recorded-tier=full --recorded-report-dir tmp/recorded-reports
python3 -B -m scripts.function_tracer_pcode.tests.tools.recorded_corpus_aggregate   --reports-dir tmp/recorded-reports
```

**A fixture replay is not a substitute for real-binary verification.** The
recording proxy is not a Java object, so Ghidra's `isinstance` / Java static-API
paths fall back to the object-API branches during recording as well as during
replay; the fixture reproduces that recorded run, not necessarily a proxy-free
CLI run. Keep running the fixed subset on real binaries for regression evidence.
`scripts/function_tracer_pcode/tests/fixtures/pcode/SCHEMA.md` documents the
format, what is recorded, the identity surrogates, and the measured determinism.

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

### Identical binary / identical function fast path

A pair whose two inputs are the same bytes and whose two function names are the
same is decided from an identity proof instead of an analysis (Issue #15). The
fast path fires only when every one of these is observed:

* the two `--binary-ids` inputs have the same `sha256` content identity, and the
  two function names are equal;
* `Program.getExecutableSHA256()` of **each** side equals **that side's** input
  sha256 (two programs agreeing with each other but not with the inputs is not
  enough);
* exactly one function of that name exists in each program;
* entry point, body range, image base, language ID and compiler spec ID are equal
  on both sides.

The proof is an artifact bound to this execution (result occurrence, execution
identity digest, both binary IDs, content identity, function name, observation
contract ID). It is emitted as the existing `EQ_CLOSURE` decisive proof, so the
outcome still comes from the one canonical decision gate; if the artifact does
not match the session, nothing is emitted and the pair is saved as a canonical
`ERROR`, never as `EQUIVALENT`. No decompiler, analyzer or solver runs when the
fast path fires.

`--no-identical-fast-path` turns the early decision off (the default is on) while
keeping the identity observation, so an unmodified run can be used as an oracle.
The result JSON carries:

* `identical_fast_path_disposition` — `{applicable, applied, reason}` (plus
  `sha_mismatch_side` when a side's sha differs), present only for pairs whose
  two inputs share one content identity and one function name;
* `decisive_proof_provenance` — `{kind, proof_artifact_digest, artifact}`, present
  only when the fast path decided the pair;
* `identical_function_identity_evidence` — `{schema, left, right}`, the identity
  observed on each side, written only after both sides' sha were checked against
  the session inputs. This is what the soundness gate reads to confirm that one
  and the same function was compared; it is deliberately **not** stored in
  `function1_identity` / `function2_identity`, which stay the per-side key that
  distinguishes one result from another (two pairs that share a byte-identical
  binary must not collapse into one result in `root_blocker_summary`). On a pair
  the fast path decided there is no analysis to derive that key from, so it is
  the observed identity scoped by the side's binary ID
  (`identical_fast_path_function_identity_v1`).

Pairs that are not identical keep their previous result JSON unchanged.

Both matrix runners take `EQBENCH_IDENTICAL_FAST_PATH` (`1` by default; `0`
passes `--no-identical-fast-path` to every pair) and record the mode in
`run_manifest.txt` as `identical_fast_path=` next to
`analysis_config_schema=eqbench-analysis-config-v3`. The flag is part of the
typed analysis config, so an ON run and an OFF run have different
`analysis_config_digest` values and neither reuses the other's pair statuses.
A run recorded before this field existed names no schema and is read as the
previous (v2) config unchanged; the soundness gate reports its mode as
`legacy_unknown` and does not guess.

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
| **B. transition** | `capability_improvement` / `classification_change` / `regression` / `other` | A new decision is an improvement **only when axis A confirms it**. A new decision nothing can confirm is `other` with the note `decided_but_unconfirmed`, counted on its own. A decision a ground truth contradicts, and a decision that was lost, is a `regression` -- except that *losing* a contradicted decision is `other` with the note `lost_a_contradicted_decision`, since dropping a wrong answer is not a loss (nor, by itself, a gain). |
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
  by the caller and never guessed from the results — and, being a request, it
  is **never treated as evidence** (see the full-scope rule below);
  `completed_scope` (`complete` / `partial` / `unknown`) comes from the
  `--manifest` rules above, applied to every result tree the run said it would
  produce and folded fail-closed (any `unknown` wins, then any `partial`). A
  run that expected no pairs is `unknown`, not `complete`. A run whose
  `subset_manifest.txt` says `scope=all` but whose `neq/` directory is absent
  is `unknown` too: the missing tree took its publication manifest with it, so
  the size of the gap is unknowable, and the tree is named in
  `coverage.trees_missing` so it cannot disappear from the counts. There is
  deliberately **no single `full_evaluation` boolean**.
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

- **A full verdict is built from a formally published artifact, never from the
  request.** `requested_scope` is a request, so it is not evidence of anything.
  `list` answers "has everything been evaluated at the current HEAD?" with
  `YES` for a scope only when a row satisfies *all* of:

  1. the run is a single whole-benchmark matrix tree — a subset run's `eq` /
     `neq` halves are by construction not one, whatever scope was requested;
  2. that tree carries a `matrix-publication-manifest.json` which satisfies the
     repository's publication artifact contract **in full**, as judged by the
     validator that owns it
     (`execution_receipt.validate_matrix_publication_manifest`) rather than by
     any second, weaker check — so the exact field set, the schema tag, the
     `run_scope`, its agreement with `analysis_config.run_scope`, the
     `analysis_config_digest` over that config, the `artifact_digest` over the
     body and the typed analysis config are all bound together;
  3. `run_manifest.txt` records a `run_scope` and it agrees with the published
     one;
  4. the **validated** analysis config shows no `sample_filter`, `pair_filter`
     or `max_samples` narrowing;
  5. the recorded scope matches the requested full scope;
  6. the tree's three artifacts are bound to **one execution** (below);
  7. the manifest's own **scope health** is `ok` (below);
  8. `completed_scope` is `complete`;
  9. `code_matches_head` is `yes`.

  **Execution binding.** A result directory gets reused, and its artifacts are
  written at different moments — `run_manifest.txt` early, the publication and
  the signed receipt at the end. A run interrupted after rewriting the manifest
  but before republishing therefore leaves one execution's publication beside
  another execution's manifest, and every individual check still passes: the
  ledger would read current provenance off the new manifest while the coverage
  came from the old run. So the tree's `validation-execution-receipt.json` must
  validate against its own `pair-status-verification-key.json`
  (`execution_receipt.validate_execution_receipt`), bind to the publication
  (same `execution_kind`, the receipt's `artifact_sha256` matching the
  publication file's actual SHA-256, and the same `analysis_config_digest` and
  source-tree digests — the shared
  `execution_receipt.matrix_execution_binding_mismatch` predicate, which the
  resume path uses too), and `run_manifest.txt` must repeat the same
  `analysis_config_digest` and `analysis_source_digest_start`/`_end`. Missing,
  malformed, unsigned or disagreeing all fail closed, and `list` prints which
  field disagreed.

  Those three digests are not execution-unique, though — the same source and
  config give the same values on every run — so a directory reused for a second
  run of the *same code* can still hold run A's publication beside run B's
  manifests and censuses and agree on all of them. The last step therefore
  rebuilds the publication from what is on the tree right now, with the builder
  that owns the canonical body
  (`execution_receipt.build_matrix_publication_manifest`), and requires it to
  equal the one that was stored. Any difference in completed/skipped samples,
  scheduled/reused pairs, failure counters, the expected or verified-skipped
  census, build receipts, binary accounting or the function census shows up as
  a different canonical body, and a tree that cannot be rebuilt at all fails
  closed too. The historical `all_eq_matrix_current` is a real example: its
  publication and its `run_manifest.txt` carry different digests and the
  manifest has no `analysis_source_digest_end`, because the directory was reused
  and the last run never finished.

  The receipt is used only to prove *which execution* the artifacts came from.
  Its `exit_status` is recorded as a diagnostic and is never a coverage
  condition, for the same reason as above: the runners fold benchmark gate
  failures into their exit code.

  **A well-formed artifact whose remaining census is complete is still not a
  full verification if the benchmark target shrank while the run was going.**
  An Eq function-census failure, for instance, records the divergence and lets
  the run continue, so `total_functions`, the pair count and the census are all
  rebuilt from the *reduced* function set and every self-consistency check
  passes — 99 functions × 120 pairs, all statuses present, `complete` — while a
  hundredth function was never evaluated. Scope health therefore reads the
  failure counters and the accounting the same validated manifest already
  carries, and requires all of: `function_census_failure_count`,
  `compile_failure_count`, `missing_binary_count` and `run_pair_failures` all
  zero; `dry_run` zero; `completed_samples + skipped_samples == target_sources`;
  `compiled_binary_count == expected_binary_count` (and non-zero);
  `total_scheduled_pair_jobs + total_skipped_pair_jobs == total_pair_jobs`. A
  field that cannot be read makes health `unknown`, never `ok`. The counter that
  decided a failure is named in `list`, so a `NO` can be traced to its number.

  `run_pair_failures` counts pair jobs that exited non-zero — a pair that
  failed canonical classification or a run-health check, i.e. one nobody could
  evaluate. A TIMEOUT or ERROR *outcome* does not bump it (the fixed subset
  carries five such pairs with `run_pair_failures=0`), so it is a coverage fact,
  not a verdict about results. The benchmark gate is deliberately **not** part
  of scope health: it lives in `benchmark_gate_failures`, which is not a
  publication-manifest field at all. A run that executed every pair and then
  failed the gate keeps its coverage fact and reports the gate failure on the C
  axis — the run's exit status is recorded as a diagnostic only, never as a
  scope condition, precisely because the runners fold gate failures into it.

  Nothing is inferred from a source that is absent: a missing manifest, a
  missing `run_scope`, a disagreement, or filters that cannot be read are each
  a recorded *reason for no* — never a field quietly dropped from the
  comparison. A subset run, a focused run, a narrowed run, a malformed artifact
  and a legacy artifact that predates the current schema therefore all answer
  `NO`, and `list` prints why. A stale full run stays a valid record of its own
  commit while answering `NO` for HEAD. Passing `--requested-scope full_eq` to
  a subset run changes nothing at all.

  A malformed publication manifest is a diagnostic, not a crash: `record` and
  `list` still work, that row simply establishes no full evidence and says why,
  and the other rows still print.

`list` names the last run *requesting* each full scope (labelling it as a
request, with its whole-benchmark evidence stated separately), then prints a
detail block for the latest run requesting each full scope, for the latest run
that actually *supports* each verdict when that is a different row, and for
every run recorded after the newest of them — each row once. `--limit` trims
the trailing verification runs and never the rows a verdict rests on. Then
comes the verdict. A ledger holding only subset rows can never print
"full verified": **subset verification is not full verification**, and a subset
row says nothing about the pairs outside the subset.

One narrowing knob is deliberately caught by a different rule: a rerun manifest
(`EQBENCH_RERUN_MANIFEST` / `NEQ_RERUN_MANIFEST`) shrinks
`expected_pair_status_paths` without appearing in the typed analysis config at
all, so a rerun of a handful of pairs can declare `FULL_EQBENCH` with empty
filters and still be `complete` against its own census. The ledger therefore
also requires the published census to cover the extent the same manifest
declares (`total_functions` × `expected_pairs_per_function`); a manifest that
contradicts itself is never evidence. The run manifest's own filter fields must
agree with the published config too — a source that is silent is a reason to
say no, not one fewer source to agree.

Each row prints `requested_scope`, `completed_scope`, `coverage`, the run
layout and declared run scope, `commit`, `dirty`, `manifest_sha256`,
`analysis_config_digest`, the whole-run timing with its source,
`code_matches_head` and any `stale_code` mark, so the conditions a run was
verified under can be retraced from the ledger alone. Where a value legitimately
differs between the halves of one run — an Eq half and a Neq half really do run
under different analysis configs — the row shows `differs` **followed by each
tree's own value**, which is a different thing from `unknown` (nobody recorded
one). The whole-run `start_time_utc` / `end_time_utc` / `hostname` come from
`subset_manifest.txt` for a subset run, because a subset legitimately starts
before its first half and ends after its last; each half's own clock is kept
under `timing.trees`.

The three axes are stored as three separate groups of counters, exactly as
`outcome_transition --axes` computes them, and are never folded into one
`PASS`. Rows also carry the run's provenance, timings, settings, outcome
counts, the persisted gate verdicts (a gate whose artifact is absent is
`unknown`, never `PASS`) and an `unresolved_variance` list to fill in by hand
when an indicator moved and a rerun did not settle whether it was the code or
run-to-run noise.

Check soundness against what is actually *verified* about each pair (exit 1 on
any violation, exit 2 when no pair status was found):

```bash
python3 -m scripts.function_tracer_pcode.reporting.soundness_gate \
    logs/EqBench/subset_after/eq logs/EqBench/subset_after/neq
```

The shared gate (`soundness-gate-v2`) fails on, and only on:

- a **verified** contradiction of a function-level reviewed relation: the
  pair's own `(sample, function)` is `CONFIRMED_EQ` in
  `function_diff_manifest.json` and was judged `NOT_EQ`, or `CONFIRMED_NOT_EQ`
  and judged `EQUIVALENT`. The lookup is done for `Eq` samples too — the
  dataset directory a sample sits in is not itself a reviewed relation;
- the same contradiction in the assumption-dependent column, but only when
  **every** premise of that pair's conditional receipt is recorded `verified`
  in `scripts/eqbench/ground_truth_conditional_compatibility.json` (the file is
  evaluation metadata; the checker never reads it, and no entry is `verified`
  today). An unverified, not-applicable or absent premise leaves the row an
  investigation;
- an identical-input pair whose identity evidence confirms the same function on
  both sides and that was judged `NOT_EQ` (any mode);
- with the fast path `on`, an applicable identical pair that was not accepted,
  or one whose disposition cannot be read (`unverifiable`);
- a configuration or integrity failure: a `eqbench-analysis-config-v3` manifest
  without a usable `identical_fast_path`, an `off` run whose results say the
  fast path was applied, a conditional column that does not hold together, a
  ground truth that is unreadable or that claims `CONFIRMED_*` without the
  evidence column, broken compatibility metadata.

Both things the gate calls *verified* have to carry their authority with them.
A reviewed relation comes from `scripts/eqbench/neq_ground_truth.tsv`, whose
evidence column is required (an `Eq` sample's relation carries
`eq_sample_single_source`); a `CONFIRMED_*` entry that reaches the gate without
evidence fails it rather than quietly becoming an investigation. A `verified`
compatibility entry must carry a real `evidence` (not `none`), a `verified_by`
and a `verified_at` UTC instant (`YYYY-MM-DDTHH:MM:SSZ`); the other statuses
must carry neither verifier field. A file the loader cannot fully understand —
an unknown field, a missing one, a duplicate key — is refused whole, so a
broken entry can never authorize a conditional violation.

A pair the runner killed at its deadline leaves no result JSON, so there is
nothing to observe: its identity is never reconstructed from the input sha
alone, it is reported as `same_function_unverified`, gate A stays silent about
it, and with the fast path `on` gate B fails closed on it (`unverifiable`).

A dataset-label mismatch, an unregistered function, an `UNKNOWN` verdict and an
unverified premise are counted and reported as investigations; they never fail
the gate. `UNKNOWN` / `TIMEOUT` / `ERROR` decide nothing and never violate
anything.

The shared gate says nothing about benchmark coverage, so both runners
separately end with the function-level
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
fix) the benchmark validation gate fails on the 192 raytrace constructor pairs
whose reviewed ground truth is `CONFIRMED_NOT_EQ` and counts the 50
`CLEVER/UnchLoop foo` pairs as suspicious (source changed, equivalence not
confirmed at the binary level). The manifest's `observed_baseline`
section records what the checker produced at the recorded commit; it is
explicitly *not* ground truth — an EQUIVALENT/NOT_EQ there may be an accident
of an implementation defect — and must only be used to explain transitions.

### Comparing two runs on the same binaries

A before/after comparison only means something when both runs analysed the same
bytes. `scripts/eqbench/binary_manifest.py` answers that from the runs
themselves — it reads the sha256 each pair's signed execution target names, so
it describes the binaries that were compared rather than whatever is on disk
now:

```bash
python3 -m scripts.eqbench.binary_manifest build \
    --run-dir logs/EqBench/<run> --binary-root . --output logs/EqBench/<run>/binary_manifest.txt
python3 -m scripts.eqbench.binary_manifest compare \
    --before logs/EqBench/<before>/binary_manifest.txt \
    --after  logs/EqBench/<after>/binary_manifest.txt
```

`compare` succeeds only when the two manifests name the **same set of keys**
(`sample_identity`, `binary_id`, path) **and** the same digest for every key: a
binary that appeared, disappeared, moved or changed all fail the same way,
because any of them makes an outcome difference ambiguous. Only a full
lower-case sha256 counts as a digest, so two runs can never look equal because
neither carried a usable one. `--binary-root` asserts that the compared tree is
still there: every binary is re-hashed under it and a **missing** file fails
just like a changed one — omit the option when the working root is gone and you
only want the manifest. Run `compare` before using two runs as before/after of
each other.

`outcome_transition --reason-sets` says which pairs it could actually compare.
A pair without a readable result payload is `incomparable`, never a match, and
the report splits that bucket by **how the pair ended, as the pair-status
authority confirms it** — not by the canonical outcome and not by the
`supervisor_status` field on its own. `pair_status_finalization()` validates
the whole signed status (seal, field set, durable authority fields, authority
kinds, child-exit join) and answers with one of:

- `resolved` — the supervisor read the child's canonical result, so the run
  holds that pair's result. A missing payload here is a `payload_loss`: a real
  difference. This includes `canonical_outcome = ERROR`, which a resolved pair
  reports just as a durable failure does.
- `durable` — a validated `TIMEOUT` or `ERROR` finalization: the pair never
  reached a canonical result and owes no payload. Whether a killed child
  flushed one first is a matter of milliseconds and differs between runs of the
  same commit.
- `unverified` — anything the authority could not confirm: an unsigned or
  edited file, a missing verification key, an ending that contradicts the
  outcome, missing durable authority fields, a broken child-exit join. This
  counts as a loss. A file that merely *says* `TIMEOUT` is not a pair that
  timed out, and "we do not know how it ended" must not become "it owed
  nothing".

An oracle comparison therefore requires `changed`, `reason-set mismatch` and
`payload_loss` to all be 0; `incomparable` alone is not a defect.

Runs are made against a fresh writable copy of the benchmark tree, never against
the canonical `targets/EqBench` checkout (the runners write compiled binaries
into their input root):

```bash
W=tmp/eqbench-work/<eqbench commit>
[[ ! -e "$W" ]] || { echo "working root exists: $W" >&2; exit 1; }
mkdir -p "$W/benchmarks" && cp -a targets/EqBench/benchmarks/. "$W/benchmarks/"
export EQBENCH_ROOT="$PWD/$W/benchmarks" NEQ_ROOT="$PWD/$W/benchmarks"
```

## Branching

`main` is the integration branch. Start every piece of work from the latest
`main` (`git switch -c <topic> main`) and merge back when done; do not keep
long-lived side branches.
