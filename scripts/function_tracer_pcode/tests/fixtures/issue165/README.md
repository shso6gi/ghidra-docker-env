# Issue #165 evidence

Test and evidence files only: production code never imports this directory.
Everything here is reproducible from a PR checkout with the repository container.

## Environment

| item | value |
|---|---|
| image | `ghidra-docker-env:latest` built from `Dockerfile` (`docker compose build`) |
| Python | 3.10.12 |
| pytest | 9.0.3 |
| z3 | 4.16.0 (not used by these files) |
| base commit (before) | `d64aba90ba78b267cd513b3e47b4d82eefdbb345` (PR #193 merge) |

A worktree needs `.env` (`DOCKER_UID` / `DOCKER_GID`) next to `docker-compose.yml`.

## Files

| file | what it is | command |
|---|---|---|
| `probe_terminal_authority.py` | 13 real-child scenarios; prints the projection, the supervisor exit code and the production classifier's verdict per invocation | `docker compose run --rm -T ghidra-dev python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue165.probe_terminal_authority` |
| `probe_terminal_authority.before_d64aba9.jsonl` | output on the base commit (the failures #165 fixes) | copy `__init__.py` and `probe_terminal_authority.py` into a checkout of `d64aba9` at the same path, run the command above |
| `probe_terminal_authority.after.jsonl` | output on the PR head (a second run gives the same bytes) | the command above |
| `phase0_gates.py` | plan v5 §10 gates G1–G3 against real child stores | `... -m scripts.function_tracer_pcode.tests.fixtures.issue165.phase0_gates` |
| `phase0_gates.head.jsonl` | its output on the PR head | |
| `terminal_model.py` | gate G4: reachable-state model of every durable publication boundary, driving the production `next_step` | `... -m scripts.function_tracer_pcode.tests.fixtures.issue165.terminal_model` |
| `terminal_model.head.json` | its summary on the PR head | |
| `runner_child.py` | T18 stand-in for the Ghidra CLI under the real `run_pair` (see `test_issue165_runner_terminal.py`) | not run directly |

| file | sha256 |
|---|---|
| `probe_terminal_authority.before_d64aba9.jsonl` | `c189d794d630b3d1eab899bb5bfa29f3e09c624dbb5c692d751c3e87d0706d8e` |
| `probe_terminal_authority.after.jsonl` | `0f32e6033b051ca5c368785e30df0c0215a2f4971ddd3a648df6323dec265f05` |
| `phase0_gates.head.jsonl` | `b060aefaa8daac516011ecec5ea7ce337deae21d959a3e0ceb96ac328dd7376b` |
| `terminal_model.head.json` | `4c6a2bbfa508904325256232c0d44e1c6fc5d271e974b0a477e200407d8b37ba` |

## Before / after (`probe_terminal_authority`)

| scenario | before (`d64aba9`) | after |
|---|---|---|
| deadline, no checkpoint / ACTIVE / RESOLVED | TIMEOUT, classified TIMEOUT | same |
| deadline at continuation-before-CAS / READY | exit 0 `RESOLVED` (`CheckpointStateTransitionReceipt`), classifier `FileNotFoundError` (no envelope) | exit 124 TIMEOUT, classified TIMEOUT |
| runner mode, RESOLVED checkpoint, exit 0 without envelope | exit 0 `RESOLVED`, classifier `FileNotFoundError` | exit 2 INVALID `CANONICAL_CHILD_RESULT_INVALID` |
| supervisor-only mode, RESOLVED checkpoint, exit 1 | exit 0 `RESOLVED`, classifier `FileNotFoundError` | exit 1 ERROR (`NON_DECOMPILATION`), classified ERROR |
| corrupt envelope, then restart | INVALID, then exit 0 `RESOLVED` on restart | INVALID both times |
| supervisor crash after `claimed.json`, restart | INVALID `NONFINAL_ACTIVE_WITHOUT_DEADLINE_AUTHORITY` | TIMEOUT, classified TIMEOUT |
| canonical TIMEOUT / UNKNOWN controls, no-checkpoint exits | unchanged | unchanged |

## Phase 0 gates

The gates were first run during Phase 0, when only the D / E / A schema layer and the
archive module existed (the supervisor did not produce E yet). `phase0_gates.py` keeps
the same checks in a form that runs on the PR head: G1 reads the E that the production
supervisor wrote, and G2 crashes the supervisor right after E so that the live chain is
still there.

| gate | result |
|---|---|
| G1 E receipt | satisfied: E is signed with the supervisor role, persisted, re-read and validated against the launch; a receipt that claims the E kind under the worker role is rejected; tampering is rejected; its measured rc joins the CLI code and the classifier accepts; a natural-exit E cannot claim signal facts; no rc exists without E |
| G2 archive adapter | satisfied: every split of a real chain (0–6 members moved) resumes from A + the live/history union; tampered member, member missing on both sides, extra history file, tampered manifest and a manifest bound to another E are rejected |
| G3 ACTIVE error stage | **not satisfied** for `DURING_DECOMPILATION`: the ERROR issuer rejects it ("supervisor deadline stage is not sealed"), so a natural exit inside decompilation stays INVALID (`ACTIVE_EXIT_STAGE_UNSEALED`). `NON_DECOMPILATION` goes through the classifier, the pair-status seal and the CLI |
| G4 state model | satisfied after one design fix found by the model (below) |

## Model (`terminal_model.py`)

The model's state is the set of durable artifacts of one store. Every production
operation is written as the sequence of its durable publications (a write, a rename or a
state replacement), in the order the production code performs them:

| step (`StepKind`) | production operation | publications, in order |
|---|---|---|
| (child) persist ACTIVE | `DurableCheckpointStore.persist_active` → `_commit_pending_active_locked` | pending transaction; predecessor members moved to history (state last); prefix stream; checkpoint; `state.json` (ACTIVE); pending removed |
| (child) completion | `worker_publish_completion` | continuation stream; continuation; `ready.json`; `state.json` READY; `state.json` RESOLVED |
| (supervisor) D | `persist_deadline` | `deadline.json` |
| (supervisor) E | `record_child_exit` | `child-exit.json` |
| `COMMIT_PENDING_ACTIVE` | `_commit_pending_active_locked` | as in the child's commit |
| `BOOTSTRAP_ACTIVE` | `issue_deadline_bootstrap_checkpoint` + `_persist_active_locked` | as in the child's persist ACTIVE |
| `RECOVER_READY` | `_recover_completion_ready_locked` | `recovery-resolution.json`; `ready.json` (same bytes); `state.json` RESOLVED |
| `CLOSE_CONTINUATION` | `_close_continuation_locked` | `recovery-resolution.json`; `ready.json`; `state.json` READY; `state.json` RESOLVED |
| `CLAIM_TIMEOUT` | `_claim_timeout_locked` | `claimed.json`; `state.json` CLAIMED |
| `FINALIZE_TIMEOUT` | `_finalize_timeout_locked` | `timeout.json`; `terminal-segment.json`; `terminal-stream.json`; `state.json` TIMED_OUT |
| `ISSUE_CANONICAL_RESOLVED` | `_write_json_locked` | `canonical-resolved-receipt.json` |
| `BEGIN_ARCHIVE` | executor in `terminal_transaction` | `archive-intent.json` |
| `ADVANCE_ARCHIVE` | `checkpoint_archive.move_remaining` | one rename per member (state last) |
| `FINALIZE_ERROR` | `_finalize_operational_error_locked` | error receipt; segment; stream; bundle |
| terminal | `ProcessSupervisorCommand._write_projection` | projection |

The reachable set starts from every child publication prefix (0, 1 or 2 checkpoints,
with or without an envelope) × natural exit / deadline × both modes × E durable or not,
and closes over a supervisor crash after every publication, restarts included. The
expected terminal comes from `expected_terminal`, which reads only the scenario (how far
the child got, how it ended, whether E became durable, the mode, the envelope) and never
calls `next_step`. The real-process tests (`test_issue165_supervisor_terminal.py`) take
their expectations from the same function, so the model and the real stores are checked
against one specification.

Checks: every reachable state drives to its oracle terminal (INVALID down to the code);
no cycle; every progress operation changes the durable state; `next_step` never raises;
every INVALID carries a code and a detail. A separate malformed / tampered set (D, E, A,
pending or live chain invalid; foreign live chain; ERROR + TIMEOUT; RESOLVED + D;
TIMEOUT + RESOLVED; claim disposition ≠ E) must be rejected by the first decision, before
any write; adding unrelated old history must not change the terminal.

The first run of the model found a real gap: while a bootstrap commit is moving the
predecessor chain into history, the live chain is "in transaction" and the bootstrap's
predecessor could not be attributed to the chain E observed, so a legitimate deadline
path ended INVALID. The snapshot now reports the predecessor's identity during the
transaction. The model does not represent the byte content of files; the real-process
tests cover the byte-level windows it cannot (for example a worker `ready.json` published
before its `state.json` swap, which recovery must adopt rather than overwrite).

Result on the PR head: 1307 reachable states, 10566 crash transitions, cycles 0,
unhandled 0 (`terminal_model.head.json`).
