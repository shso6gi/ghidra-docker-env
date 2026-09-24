"""OS process の同一性（PID + start token）と生存の観測。

PID は再利用されるので、process は ``/proc/<pid>/stat`` の開始時刻と組にして
名指す。この module が同一性の規則の唯一の owner で、supervisor の起動
（``supervisor_command``）・worker の自己申告（``worker_runtime``）・終端の
判断に渡す生存の観測（分類器・restart）が同じ関数を使う。

標準 library しか import しない（supervisor の CLI や store に依存しない）。
"""

from __future__ import annotations

from pathlib import Path
from typing import Optional

_PROC = Path("/proc")


def read_process_start_token(pid: int, *, proc_root: Path = _PROC) -> str:
    """``pid`` の process の start token（開始時刻。読めなければ ValueError）。"""

    if type(pid) is not int or pid <= 0:
        raise TypeError("process PID is invalid")
    try:
        stat = (proc_root / str(pid) / "stat").read_text(encoding="utf-8")
        closing = stat.rfind(")")
        fields_after_comm = stat[closing + 2:].split()
        start_time = fields_after_comm[19]
    except (OSError, IndexError, ValueError) as exc:
        raise ValueError("process start token is unavailable") from exc
    if not start_time.isascii() or not start_time.isdecimal():
        raise ValueError("process start token is not canonical")
    return f"linux-proc-starttime-{start_time}"


def process_is_alive(pid: int, start_token: str) -> Optional[bool]:
    """PID + start token の process がいま動いているか（zombie は終了扱い）。

    start token が読めない・一致しないなら、その process はもう居ない（False）。
    start token は一致したのに、続けて読む ``stat`` が読めなかったときだけ
    None（分からない。その間に終わった可能性がある）。
    """

    try:
        if read_process_start_token(pid) != start_token:
            return False
        stat = (_PROC / str(pid) / "stat").read_text(encoding="utf-8")
    except ValueError:
        return False
    except OSError:
        return None
    return stat[stat.rfind(")") + 2:stat.rfind(")") + 3] not in {"Z", "X"}
