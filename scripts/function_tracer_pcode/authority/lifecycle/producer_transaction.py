"""Producer transactions of one pilot session: boundary, attempts and ownership (plan v4 PR-A).

A *producer transaction* is one attempt to publish one signal object: the
judgement against the producer ledgers, the reservation, the encoding, the
publication with its producer / external / Phase 7 commits, and then either
the end-of-transaction hook (published) or the rollback (failed).

Three identities are kept apart:

* the **signal object** (``id(signal)``): encoders key their in-flight state
  (pending emission, rollback snapshot) and the session keys the Phase 7
  wrapper transaction by it.  So at most one attempt per signal object may be
  live at a time; a second attempt for the same object is refused *before it
  acquires anything*, and its refusal releases nothing (everything keyed by
  that object belongs to the live attempt).
* the **occurrence** (the cause identity): owned by the domain ledgers; two
  different objects with the same content are two attempts on one occurrence
  and are serialized by the boundary, the ledger decides between them.
* the **attempt** (``ProducerAttempt``): what one call owns.  Rollback and
  cleanup apply only to the resources the attempt recorded as acquired.

Stages of an attempt and who may change what:

* not admitted -- refused: nothing was acquired, nothing is released (the
  refusal is recorded as a producer failure: the pair is ERROR).
* PREPARING  -- admitted; the attempt owns its Phase 7 wrapper transaction
  (when it claimed one) and, once it calls the encoder, the encoder's
  in-flight state for its signal object.
* COMMITTING -- the producer commit has started.  As in every stage of a live
  attempt, no other attempt may start and no direct publication may be
  staged, so the rollback state of this attempt describes only its own
  changes.  Commits that belong to this attempt (an ABI transaction committing
  its transformed SAT-safety observation through the encoder's commit API)
  are not new attempts and run inside it.
* PUBLISHED  -- the events are appended; nothing may undo them.  The
  end-of-transaction hook runs; its failure is recorded and propagated, the
  events stay.
* ROLLED_BACK -- the attempt's own resources were restored.
* ENDED      -- the signal object is free again.

The boundary (one reentrant lock, the outermost authority lock) serializes
attempts across threads; the attempt registry (one live attempt per session)
and the publication guard refuse reentry from the same thread.  The lock is released by the context manager, also on
exceptions; the Phase 7 wrapper transaction holds one level of it from its
activation until the attempt that claimed it commits or rolls it back.
"""

from __future__ import annotations

from contextlib import contextmanager
from enum import Enum
from threading import RLock, get_ident
from typing import Any, Dict, Iterator, Optional


class ProducerTransactionRefused(ValueError):
    """A producer attempt or direct publication was refused before it acquired anything."""


class AttemptStage(str, Enum):
    PREPARING = "preparing"
    COMMITTING = "committing"
    PUBLISHED = "published"
    ROLLED_BACK = "rolled_back"
    ENDED = "ended"


class ProducerAttempt:
    """What one producer call owns (see the module docstring)."""

    __slots__ = ("signal", "stage", "phase7_transaction", "encoder_touched")

    def __init__(self, signal: Any) -> None:
        self.signal = signal
        self.stage = AttemptStage.PREPARING
        #: The Phase 7 wrapper transaction object this attempt claimed (None: none).
        self.phase7_transaction: Any = None
        #: The attempt called the encoder for its signal object (so the
        #: encoder's in-flight state for that object is this attempt's).
        self.encoder_touched = False


class ProducerTransactionBoundary:
    """The session's single producer transaction boundary and its attempt registry."""

    def __init__(self) -> None:
        self._lock = RLock()
        self._owner: Optional[int] = None
        self._depth = 0
        self._live: Dict[int, ProducerAttempt] = {}
        self._publishing = 0

    # ---- the lock ----------------------------------------------------------

    def enter(self) -> None:
        self._lock.acquire()
        self._owner = get_ident()
        self._depth += 1

    def exit(self) -> None:
        self._depth -= 1
        if self._depth == 0:
            self._owner = None
        self._lock.release()

    @contextmanager
    def hold(self) -> Iterator[None]:
        self.enter()
        try:
            yield
        finally:
            self.exit()

    def held_by_current_thread(self) -> bool:
        return self._owner == get_ident()

    # ---- admission -----------------------------------------------------------

    @property
    def commit_open(self) -> bool:
        """A live attempt is between its producer commit and its end (diagnostic stage)."""
        return any(attempt.stage is AttemptStage.COMMITTING for attempt in self._live.values())

    @property
    def work_in_progress(self) -> bool:
        """An attempt is live or a publication is being staged: no new producer work may start."""
        return bool(self._live) or self._publishing > 0

    @property
    def publishing_open(self) -> bool:
        return self._publishing > 0

    def live_attempt(self, signal: Any) -> Optional[ProducerAttempt]:
        attempt = self._live.get(id(signal))
        return attempt if attempt is not None and attempt.signal is signal else None

    @property
    def has_live_attempt(self) -> bool:
        return bool(self._live)

    def refuse_new_work(self, what: str) -> None:
        """Refuse a new attempt or a direct publication while another one is in progress.

        One attempt is live at a time in a session (other threads wait on the
        lock; the owning thread is refused here): a new attempt or a direct
        publication from inside a live attempt -- its preparation, its commit
        callbacks or its end-of-transaction hook -- would interleave with it.
        Work that belongs to the live attempt (its own commit API calls, such
        as an ABI transaction committing its transformed SAT-safety
        observation) is not a new attempt and does not come here.
        """
        if self._live:
            raise ProducerTransactionRefused(f"{what} inside a live producer transaction")
        if self._publishing:
            raise ProducerTransactionRefused(f"{what} inside a publication")

    def admit(self, signal: Any) -> ProducerAttempt:
        """Admit one attempt for ``signal`` or refuse it before it acquires anything."""
        if not self.held_by_current_thread():
            raise RuntimeError("producer attempt admitted outside the transaction boundary")
        if id(signal) in self._live:
            raise ProducerTransactionRefused(
                "the signal object already has a live producer transaction"
            )
        self.refuse_new_work("producer transaction")
        attempt = ProducerAttempt(signal)
        self._live[id(signal)] = attempt
        return attempt

    # ---- stages --------------------------------------------------------------

    def begin_commit(self, attempt: ProducerAttempt) -> None:
        """``attempt``'s producer commit starts (the COMMITTING stage)."""
        if self._live.get(id(attempt.signal)) is not attempt:
            raise RuntimeError("producer commit of an attempt that is not live")
        attempt.stage = AttemptStage.COMMITTING

    def end(self, attempt: ProducerAttempt, stage: AttemptStage) -> None:
        """End ``attempt`` (published or rolled back): free its signal object."""
        attempt.stage = stage
        if self._live.get(id(attempt.signal)) is attempt:
            del self._live[id(attempt.signal)]
        attempt.stage = AttemptStage.ENDED

    @contextmanager
    def publishing(self) -> Iterator[None]:
        """The events of one publication are being staged and appended."""
        self._publishing += 1
        try:
            yield
        finally:
            self._publishing -= 1
