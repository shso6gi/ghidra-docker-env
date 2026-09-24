# -*- coding: utf-8 -*-
"""pair 1 件分の診断 surface を設置する（Issue #124 PR-124-B）。

やることは 2 つだけ。

1. `--stage-journal` の path に `StageJournal` を開き、プロセスの active
   journal にする（`core/stage_journal.py`）。
2. `--stack-dump-file` の path へ Python の全 thread stack を吐く handler を
   **JVM 起動より前**に登録する。

## readiness 契約（この module の要）

``handler_registered`` を journal に書いてよいのは、
**`faulthandler.register()` が例外を出さずに return した場合だけ**である。

* `/proc/self/status` の ``SigCgt`` は ``payload.sigcgt_probe`` に**補助情報**
  として併記するだけで、readiness の根拠にしない。JVM（HotSpot）は自前の
  signal handler を多数登録するので、mask のビットが立っていることは
  「Python の faulthandler が登録されている」ことを意味しない。
* 「JVM が signal を捕捉していそう」「handler がありそう」といった推測も
  根拠にしない。
* 登録に失敗したら ``handler_registered`` は**絶対に書かず**、
  ``note: handler_registration_failed:<例外型>`` を書く。判定にも process の
  終了状態にも影響しない。

## signal の選択

``SIGUSR1`` のみを使う。理由:

* ``SIGQUIT`` は HotSpot の thread dump に使われており、JVM が先に捕まえる。
* ``SIGUSR2`` は glibc / JVM の内部（`SR_signum` の既定近辺）と衝突し得る。
* ``SIGUSR1`` は既定動作が terminate なので、**登録が確認できない限り送っては
  ならない**（送信側の責務は PR-124-C）。この PR では送信を一切行わない。

`chain=False` は「faulthandler が stack を書いたあと、**登録時点で入っていた
previous handler へ連鎖しない**」という設定である。あとから別の handler が
SIGUSR1 を上書きすることを防ぐ設定ではない（それは登録順の問題で、この flag は
関与しない）。JVM 起動後も Python の faulthandler が生きているかどうかは別問題で、
実 JVM を上げた子プロセス test（`RUN_PYGHIDRA_REGRESSIONS=1`）で実証する。

`all_threads=True` は `smt/parallel.py` の solver worker thread を dump に含めるため。

## dump path の 2 本立て

* ``dump_artifact_path``（`--stack-dump-artifact`）が**正本**。run dir 配下
  (`.runtime-metrics/<pair>.stack-dump.txt`) なので、pair 終了後の
  `process_authority_cleanup` の後も残る。
* ``dump_path_tmp``（`--stack-dump-file`）は faulthandler が実際に書く先で、
  checkpoint 配下にある。cleanup で消えるので**正本にしない**。

artifact への退避（copy）と存在確認は PR-124-C の責務で、この PR では行わない。
"""

from __future__ import annotations

import faulthandler
import os
import signal
import sys
from dataclasses import dataclass, field
from typing import Any, Dict, Mapping, Optional

from scripts.function_tracer_pcode.core.stage_journal import (
    EVENT_HANDLER_REGISTERED,
    StageJournal,
    journal_event,
    journal_note,
    set_active_stage_journal,
)

#: 診断 dump に使う signal。SIGQUIT / SIGUSR2 は使わない（module docstring）。
STACK_DUMP_SIGNAL = signal.SIGUSR1

#: `faulthandler.register()` と dump file の open で起こり得る失敗。
#: `except Exception` を足さないため（PR-125-B の baseline は delete-only）、
#: 実際に送出され得る型を列挙する:
#: - `OSError`   sigaction 失敗 / open 失敗（`io.UnsupportedOperation` を含む）
#: - `ValueError` signal 番号が不正 / file が閉じている / 主インタプリタでない
#: - `RuntimeError` handler を設置できない
#: - `TypeError` / `AttributeError` file object が `fileno()` を持たない
_REGISTRATION_ERRORS = (AttributeError, OSError, RuntimeError, TypeError, ValueError)

#: dump 先の file object は faulthandler が fd を保持し続けるので、GC で閉じ
#: られないようにプロセスの寿命の間ここで参照を持つ。
_RETAINED_DUMP_FILES: list = []


@dataclass
class PairDiagnostics:
    """設置結果。判定には使わない（呼び出し側は読むだけ）。"""

    journal: Optional[StageJournal] = None
    dump_path_tmp: Optional[str] = None
    dump_artifact_path: Optional[str] = None
    handler_registered: bool = False
    registration_error: Optional[str] = None
    dump_file: Any = None
    payload: Dict[str, Any] = field(default_factory=dict)


def _path_argument(path: Any) -> Optional[str]:
    """CLI から来た path 引数を絶対 path にする。

    `str` / `os.PathLike` 以外（未設定の `None`、テストの stub など）は
    「指定なし」として扱う。`str(value)` で無理に path 化すると、path でない
    値の名前で file を作ってしまう。相対 path を絶対にするのは、journal が
    記録する dump path を曖昧にしないため（cwd 依存の path を契約にしない）。
    """
    if not isinstance(path, (str, os.PathLike)):
        return None
    text = os.fspath(path)
    if not text:
        return None
    return os.path.abspath(text)


def _child_start_token() -> Dict[str, Any]:
    """自プロセスの start token（supervisor の launch receipt と同じ導出）。

    送信側（PR-124-C）が pid の再利用を排除するために照合する値なので、
    ここで独自定義を作らず authority の関数をそのまま使う。取得できなくても
    registration の可否には影響しない。
    """
    try:
        from scripts.function_tracer_pcode.authority.process.process_identity import (
            read_process_start_token,
        )

        return {"start_token": read_process_start_token(os.getpid())}
    except (ImportError, TypeError, ValueError) as exc:
        return {"start_token": None, "start_token_error": type(exc).__name__}


def _sigcgt_probe(signal_number: int) -> Dict[str, Any]:
    """`/proc/self/status` の SigCgt。**readiness の根拠ではない**補助情報。"""
    probe: Dict[str, Any] = {"authoritative": False}
    try:
        with open("/proc/self/status", "r", encoding="ascii", errors="replace") as handle:
            for line in handle:
                if line.startswith("SigCgt:"):
                    mask = line.split(":", 1)[1].strip()
                    probe["sigcgt"] = mask
                    probe["signal_bit_set"] = bool(
                        (int(mask, 16) >> (int(signal_number) - 1)) & 1
                    )
                    return probe
    except (OSError, ValueError) as exc:
        probe["error"] = type(exc).__name__
        return probe
    probe["error"] = "sigcgt_absent"
    return probe


def jvm_already_started() -> bool:
    """in-process JVM の起動を **この probe で観測できたか**。

    JPype が import すらされていなければ JVM は起動していない。import 済み
    なら JPype 自身に聞く。**判断できないときは False を返す**ので、この関数の
    False は「JVM は起動していない」の証明ではなく「起動を観測しなかった」で
    しかない。`registered_before_jvm` もその意味で読むこと
    （production path で登録が JVM 起動より前であることの根拠は、
    `run_equivalence_check` の呼び出し順と実 JVM 子プロセス test の
    `handler_registered` < `jvm_state_after_launch` の順序であって、この probe
    単独ではない）。
    """
    jpype = sys.modules.get("jpype")
    if jpype is None:
        return False
    probe = getattr(jpype, "isJVMStarted", None)
    if not callable(probe):
        return False
    try:
        return bool(probe())
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return False


def open_pair_journal(
    journal_path: Any, *, context: Optional[Mapping[str, Any]] = None
) -> Optional[StageJournal]:
    """journal を開いて active にし、pair の識別情報を 1 行残す。"""
    resolved = _path_argument(journal_path)
    if resolved is None:
        return None
    journal = StageJournal(resolved)
    set_active_stage_journal(journal)
    opened: Dict[str, Any] = {"journal_path": resolved}
    if context:
        opened.update(dict(context))
    journal_note("pair_journal_opened", opened)
    return journal


def register_stack_dump_handler(
    state: PairDiagnostics, *, signal_number: int = STACK_DUMP_SIGNAL
) -> PairDiagnostics:
    """dump handler を登録し、成功したときだけ `handler_registered` を書く。"""
    if not state.dump_path_tmp:
        journal_note("stack_dump_handler_not_requested", {
            "dump_artifact_path": state.dump_artifact_path,
        })
        return state

    handle = None
    phase = "open_dump_file"
    try:
        directory = os.path.dirname(state.dump_path_tmp)
        if directory:
            os.makedirs(directory, exist_ok=True)
        handle = open(state.dump_path_tmp, "ab", buffering=0)
        phase = "register"
        faulthandler.register(
            signal_number,
            file=handle,
            all_threads=True,
            chain=False,
        )
    except _REGISTRATION_ERRORS as exc:
        if handle is not None:
            try:
                handle.close()
            except OSError:
                pass
        state.handler_registered = False
        state.registration_error = type(exc).__name__
        # readiness を主張しない。理由だけを残す（送信側が判定に使う）。
        journal_note(f"handler_registration_failed:{type(exc).__name__}", {
            "phase": phase,
            "detail": f"{type(exc).__name__}: {exc}"[:200],
            "dump_path_tmp": state.dump_path_tmp,
            "dump_artifact_path": state.dump_artifact_path,
            "signal_number": int(signal_number),
        })
        return state

    # ここに来たのは `faulthandler.register()` が例外なく返ったときだけ。
    try:
        signal_name = signal.Signals(int(signal_number)).name
    except ValueError:
        signal_name = str(signal_number)
    _RETAINED_DUMP_FILES.append(handle)
    state.dump_file = handle
    state.handler_registered = True
    payload: Dict[str, Any] = {
        "pid": os.getpid(),
        # 正本は cleanup 後も残る run dir 側。checkpoint 側は別 key。
        "dump_artifact_path": state.dump_artifact_path,
        "dump_artifact_path_status": (
            "declared" if state.dump_artifact_path else "unset"
        ),
        "dump_path_tmp": state.dump_path_tmp,
        # 「登録時の probe で JVM started を観測しなかった」という意味。
        # probe 不能時も False（= この値は true）になるので、単独で
        # 「JVM より前だった」ことの証明にはしない（`jvm_already_started`）。
        "registered_before_jvm": not jvm_already_started(),
        "signal": signal_name,
        "signal_number": int(signal_number),
        "all_threads": True,
        "chain": False,
        "readiness_basis": "faulthandler_register_returned",
        "sigcgt_probe": _sigcgt_probe(signal_number),
    }
    payload.update(_child_start_token())
    state.payload = payload
    journal_event(EVENT_HANDLER_REGISTERED, stage="stack_dump_handler", payload=payload)
    return state


def install_pair_diagnostics(
    args: Any, *, context: Optional[Mapping[str, Any]] = None
) -> PairDiagnostics:
    """journal を開き、JVM 起動前に dump handler を登録する。

    **呼び出し位置の契約**: `start_headless_pyghidra()`（in-process JVM 起動）
    より前に呼ぶこと。`tests/unit/test_issue124b_stage_journal.py` が
    `run_equivalence_check` の呼び出し順を source で固定している。
    """
    state = PairDiagnostics(
        dump_path_tmp=_path_argument(getattr(args, "stack_dump_file", None)),
        dump_artifact_path=_path_argument(getattr(args, "stack_dump_artifact", None)),
    )
    state.journal = open_pair_journal(
        getattr(args, "stage_journal", None), context=context
    )
    return register_stack_dump_handler(state)
