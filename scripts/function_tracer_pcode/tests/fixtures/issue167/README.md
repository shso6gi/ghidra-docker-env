# Issue #167 evidence

Test and evidence files only: production code never imports this directory.
Everything here is reproducible from a PR checkout with the repository container.

## Environment

| item | value |
|---|---|
| image | `ghidra-docker-env:latest` built from `Dockerfile` (`docker compose build`) |
| Python | 3.10.12 |
| z3 | 4.16.0 (`z3-solver==4.16.0.0` in `requirements-test.txt`; the Python API is used) |
| pytest | 9.0.3 |
| base commit (before) | `1be9c1613c9894f89dafc5329e2410b186c1c091` |

A worktree needs the main repository's `.git` mounted read-only, or git inside the
container exits 128:

```bash
docker compose run --rm -T \
  -v "<main checkout>/.git:<main checkout>/.git:ro" ghidra-dev <command>
```

## Root-cause probe (`probe_root_cause.py`)

Builds its inputs in code (`create_mock_analysis`, no binaries), runs the production
normalizer, `FormulaBuilder` and SMT lowering, and asks z3.

```bash
docker compose run --rm -T ghidra-dev \
  python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue167.probe_root_cause
```

To reproduce the *before* output, copy `__init__.py` and `probe_root_cause.py` into a
checkout of `1be9c16` at the same path and run the same command.

| file | sha256 |
|---|---|
| `probe_root_cause.before_1be9c16.jsonl` | `ab4ba7647054417202d6c11177c6a26a573c3e6cfd7a921a214699769b57c86c` |
| `probe_root_cause.after.jsonl` | `d36ef6debe1d0bfbf32fe3acf7124e951a32b2ef18c0aab9c849d306416f76c8` (re-run on the PR head gives the same bytes) |

| probe | before (`1be9c16`) | after | meaning |
|---|---|---|---|
| W1 cross-use hint | 64-bit `x == 0` becomes `(extract 31 0 x) == 0` | unchanged `(= x (_ bv0 64))` | a single-use hint is no longer an input assumption |
| W6 | monolithic `unsat` (false EQUIVALENT) | `sat` | `x = 1<<32` separates `x == 0` and `(int)x == 0` |
| W3 | monolithic `sat` (false NOT_EQ on identical functions) | `unsat` | the premise tie is no longer narrowed by a hint |
| bare arithmetic | `x + 1` (64) rewritten to 32 bit | unchanged | sort change removed |
| signed/unsigned | `sext(low p) <u 16` rewritten to `low p <s 16`, differs (`sat`) | unchanged | conversion removed |
| mask parent sort | ill-sorted rewrite (z3 sort error) | `zext(low p)`, `unsat` | parent sort and full value kept |
| DIV composite | SDIV of zero-extended operands narrowed, differs (`sat`) | unchanged | operand expression must be a sign image |
| independent fragment | `PIECE(hi, x)` collapsed to `sext(x)`, differs (`sat`) | unchanged | fragment collapse removed |

## Decision model (`decision_model.py`)

An independent rewrite of v5 §4.5 (R0–R5) that imports nothing from the repository.
The v4 scratch model (`md5 2dfdcb1a26b2...`) could not be retrieved, so the 16 v4 cases
were reconstructed from the v5 text.

```bash
python3 -B scripts/function_tracer_pcode/tests/fixtures/issue167/decision_model.py
# expected last line: cases=16 fail=0
```

`tests/unit/test_input_correspondence_decision_model.py` checks the production
`build_input_correspondence_set` against this model for all 324 side combinations of
width {32, 64} × raw read width {16, 32, bare} × IEE {none, SIGN32, ZERO32, SIGN16}.

## Rule certificates

`tests/unit/test_semantic_width_rule_certificates.py` certifies every rule in
`semantic_width.SEMANTIC_WIDTH_RULES` with the real rule and the real lowering.
For division, z3 does not decide the universal 64→32 equivalence of two dividers
within 60 s. The universal certificate is therefore taken at 16→8 in the unit suite,
and the production width 64→32 is checked on every pair of boundary values. The
identity is width-generic under SMT-LIB `bvsdiv/bvsrem/bvudiv/bvurem`, division by
zero and `INT_MIN / -1` included. Measured on this image (seconds, `unsat` =
certified, `unknown` = 60 s timeout):

| W→N | bvsdiv | bvsrem | bvudiv | bvurem |
|---|---|---|---|---|
| 16→8 | 0.03 unsat | 0.06 unsat | 0.03 unsat | 0.05 unsat |
| 32→16 | 8.37 unsat | 15.42 unsat | 11.74 unsat | 28.28 unsat |
| 64→32 | 60 unknown | 60 unknown | 60 unknown | 60 unknown |

The universal division check, for re-running (slow for 32→16):

```bash
docker compose run --rm -T ghidra-dev python3 -B - <<'PY'
import time, z3
for W, N in ((16, 8), (32, 16)):
    for op, ext in (("bvsdiv", "sign_extend"), ("bvsrem", "sign_extend"),
                    ("bvudiv", "zero_extend"), ("bvurem", "zero_extend")):
        s = z3.Solver()
        s.from_string(
            f"(declare-const a (_ BitVec {N}))(declare-const b (_ BitVec {N}))"
            f"(assert (distinct ((_ extract {N-1} 0) ({op} ((_ {ext} {W-N}) a) ((_ {ext} {W-N}) b))) ({op} a b)))"
        )
        t = time.time(); print(W, N, op, s.check(), round(time.time() - t, 2))
PY
```

## Fixed subset before/after

The pair set, settings and binaries are fixed; the results are in the PR body
(the run has to be on the final head, so this file cannot carry them).

| item | value |
|---|---|
| subset manifest | `scripts/function_tracer_pcode/reporting/eqbench_subset.json`, sha256 `c38c0df03e42787dd2582aa85cc6d654ec9c024eb61296ed40dc1977edab62fa` (Eq 8 sources × 8 pairs = 64, Neq 80) |
| working root | a fresh clone of the canonical `targets/EqBench` at `3724fce5b287cc63165028444daf904f25b0158b` under `tmp/issue167/eqwork/` of each checkout (the runners refuse roots outside the repository); the canonical checkout is never written |
| binaries | built into each working root before the measured runs, which use `EQBENCH_BUILD_POLICY=PREBUILT_ONLY`; the binaries each run actually compared are proven identical with `scripts.eqbench.binary_manifest`: Eq 112 binaries, manifest sha256 `86fb1f124770385eb58473eff3b9e91f2811a045e5d9259b9ac29dfacb9e4044`; Neq 140 binaries, `d4c56f6a94d2a8ea6b7803739943cffbeb675a52100ca00e0931f19b80da40b6` |
| settings | `PARALLEL_JOBS=20`, `PAIR_PROCESS_TIMEOUT=240s`, `EQBENCH_RESOURCE_ADMISSION=0`, `EQBENCH_IDENTICAL_FAST_PATH=1`, `EQBENCH_DEBUG=1` (the `Input correspondence:` line is a debug line), equiv 10 s, decompile 60 s, pairwise 5 s / 30 s hard |
| before | `1be9c1613c9894f89dafc5329e2410b186c1c091` in its own worktree |

```bash
# in each checkout (before: a worktree of 1be9c16; after: the PR head)
git clone -q <canonical>/targets/EqBench tmp/issue167/eqwork/EqBench   # at 3724fce5
docker compose run --rm -T -v "<main checkout>/.git:<main checkout>/.git:ro" ghidra-dev env \
  EQBENCH_ROOT=/workspace/tmp/issue167/eqwork/EqBench/benchmarks \
  NEQ_ROOT=/workspace/tmp/issue167/eqwork/EqBench/benchmarks \
  EQBENCH_BUILD_POLICY=PREBUILT_ONLY EQBENCH_DEBUG=1 \
  OUTPUT_BASE_DIR=/workspace/tmp/issue167/<label> SUBSET_ISSUE=167 \
  ./eqbench_run_subset.sh
# binaries actually compared, per half, then before vs after
python3 -B -m scripts.eqbench.binary_manifest build --run-dir tmp/issue167/<label>/<half> \
  --binary-root /workspace --output tmp/issue167/binary_manifest_<label>_<half>.txt
python3 -B -m scripts.eqbench.binary_manifest compare --before <before manifest> --after <after manifest>
# transitions
python3 -B -m scripts.function_tracer_pcode.reporting.outcome_transition \
  --before <before>/<half> --after <after>/<half> --changed-only --axes --reason-sets
```

The Neq half cannot re-run into a cleared output directory while its signing key
survives under `tmp/eqbench-private-authority-neq/` (#170); remove that keyset
directory before a re-run.
