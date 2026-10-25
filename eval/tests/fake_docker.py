#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wrapper の test 用の docker（状態は ``$FAKE_DOCKER_STATE`` の JSON）。

wrapper が使う subcommand だけを、本物と同じ出力形式で真似る。

* ``run --rm``（読み取り専用の reader と環境の probe）: ``-v`` の mount を host の path に
  読み替えて、host の python でその command を実行する（summarize.py は本物が動く）。
  probe は状態の ``probe`` の行を返す。
* ``run -d``（評価の container）: 状態に running の container を作る。中身の runner は
  動かさない。test が状態を書き換えて「終了」させる（``exit_code`` / ``oom_killed``）。
* ``wait`` は状態が exited になるまで待つ。``stop`` は exited（143）にする。
* 呼び出しはすべて ``calls`` に記録する（何を起動したかを test が確かめる）。
"""

from __future__ import annotations

import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time

STATE = Path(os.environ["FAKE_DOCKER_STATE"])


class State:
    def __enter__(self):
        self.fd = os.open(STATE.with_suffix(".lock"), os.O_RDWR | os.O_CREAT, 0o644)
        fcntl.flock(self.fd, fcntl.LOCK_EX)
        self.data = json.loads(STATE.read_text()) if STATE.exists() else {}
        return self.data

    def __exit__(self, *exc):
        temporary = STATE.with_suffix(".tmp")
        temporary.write_text(json.dumps(self.data, indent=1, sort_keys=True))
        os.replace(temporary, STATE)
        fcntl.flock(self.fd, fcntl.LOCK_UN)
        os.close(self.fd)


def find(data, name_or_id):
    for container in data.get("containers", []):
        if name_or_id in (container["name"], container["id"]) or container["id"].startswith(name_or_id):
            return container
    return None


def parse_run(args):
    options = {"mounts": [], "env": {}, "labels": {}, "detach": False, "rm": False,
               "tmpfs": [], "workdir": None, "name": None}
    index = 0
    while index < len(args):
        arg = args[index]
        if arg in ("-d",):
            options["detach"] = True
        elif arg == "--rm":
            options["rm"] = True
        elif arg == "--init":
            pass
        elif arg in ("-v", "-e", "--label", "--tmpfs", "-w", "--name", "--network", "--memory",
                     "--memory-swap", "-u", "--stop-timeout"):
            value = args[index + 1]
            index += 1
            if arg == "-v":
                parts = value.split(":")
                options["mounts"].append((parts[0], parts[1], len(parts) > 2 and parts[2] == "ro"))
            elif arg == "-e":
                key, _sep, val = value.partition("=")
                options["env"][key] = val
            elif arg == "--label":
                key, _sep, val = value.partition("=")
                options["labels"][key] = val
            elif arg == "--tmpfs":
                options["tmpfs"].append(value)
            elif arg == "-w":
                options["workdir"] = value
            elif arg == "--name":
                options["name"] = value
            else:
                options[arg.lstrip("-")] = value
        else:
            options["image"] = arg
            options["command"] = args[index + 1:]
            break
        index += 1
    return options


def holds_eval_lock():
    """この docker CLI の process が評価の lock file を開いているか（受け継いだ fd）。"""
    target = os.environ.get("EVAL_LOCK_FILE")
    if not target or not os.path.exists(target):
        return False
    wanted = os.stat(target)
    for name in os.listdir("/proc/self/fd"):
        try:
            found = os.stat(f"/proc/self/fd/{name}")
        except OSError:
            continue
        if (found.st_dev, found.st_ino) == (wanted.st_dev, wanted.st_ino):
            return True
    return False


def to_host(path, mounts):
    for source, target, _ro in sorted(mounts, key=lambda m: -len(m[1])):
        if path == target or path.startswith(target + "/"):
            return source + path[len(target):]
    return path


def operation(argv):
    """失敗の注入の key: ``run-d`` / ``run-rm`` / ``logs`` / ``rm`` / ``stop`` / ``wait`` /
    ``inspect`` / ``ps`` / ``version`` / ``image``。"""
    if argv[0] == "run":
        return "run-d" if "-d" in argv else "run-rm"
    return argv[0]


def consume_failure(data, key):
    """``fail[key]`` が正なら 1 減らして失敗、-1 なら常に失敗。"""
    remaining = (data.get("fail") or {}).get(key, 0)
    if remaining == 0:
        return False
    if remaining > 0:
        data["fail"][key] = remaining - 1
    return True


def main(argv):
    with State() as data:
        data.setdefault("calls", []).append(argv)
        failed = consume_failure(data, operation(argv))
        if failed and operation(argv) == "run-d" and data.get("create_on_failed_run"):
            # 作成までは済んで、起動に失敗した（docker run が非 0 を返しても container は残る）。
            options = parse_run(argv[1:])
            number = len(data.setdefault("containers_started", [])) + 1
            identifier = f"{number:064x}"
            container = {"id": identifier, "name": options["name"], "status": "created",
                         "exit_code": 0, "labels": options["labels"], "env": options["env"],
                         "image": options["image"], "command": options["command"]}
            data.setdefault("containers", []).append(container)
            data["containers_started"].append(dict(container))
    if failed:
        print(f"Error response from daemon: fake docker: {operation(argv)} fails", file=sys.stderr)
        return 1
    command, args = argv[0], argv[1:]
    if command == "image":
        with State() as data:
            image = data.get("images", {}).get(args[-1])
        if image is None:
            print("No such image", file=sys.stderr)
            return 1
        print(image)
        return 0
    if command == "version":
        print("29.0-fake")
        return 0
    if command == "ps":
        everything = "-a" in args
        label = None
        if "--filter" in args:
            label = args[args.index("--filter") + 1].split("=", 1)[1]
        with State() as data:
            containers = list(data.get("containers", []))
            others = list(data.get("others", []))
        for container in containers:
            if not everything and container["status"] != "running":
                continue
            if label is not None and container["labels"].get(label.split("=")[0]) != label.split("=")[1]:
                continue
            labels = container["labels"]
            if label is not None:
                print(f"{container['name']}\t{container['status']}\t{labels.get('ghidra-eval.eval', '')}")
            else:
                print(f"{container['name']}\t{labels.get('ghidra-eval.slot', '')}\t{labels.get('ghidra-eval.reader', '')}")
        if label is None:
            for name in others:
                print(f"{name}\t\t")
        return 0
    if command == "inspect":
        with State() as data:
            container = find(data, args[-1])
        if container is None:
            print(f"Error: No such container: {args[-1]}", file=sys.stderr)
            return 1
        print(json.dumps([{
            "Id": container["id"],
            "State": {"Status": container["status"], "Running": container["status"] == "running",
                      "ExitCode": container.get("exit_code", 0),
                      "OOMKilled": container.get("oom_killed", False), "Error": "",
                      "StartedAt": container.get("started_at", "2026-10-25T00:00:00.000000000Z"),
                      "FinishedAt": container.get("finished_at", "0001-01-01T00:00:00Z")},
            "Config": {"Labels": container["labels"]},
        }]))
        return 0
    if command == "run":
        options = parse_run(args)
        if options["detach"]:
            with State() as data:
                if find(data, options["name"]) is not None:
                    print("Conflict. The container name is already in use", file=sys.stderr)
                    return 125
                number = len(data.setdefault("containers_started", [])) + 1
                identifier = f"{number:064x}"
                container = {"id": identifier, "name": options["name"], "status": "running",
                             "cli_holds_eval_lock": holds_eval_lock(),
                             "labels": options["labels"], "env": options["env"],
                             "image": options["image"], "command": options["command"],
                             "mounts": options["mounts"], "memory": options.get("memory"),
                             "stop_timeout": options.get("stop-timeout")}
                data.setdefault("containers", []).append(container)
                data["containers_started"].append(dict(container))
            print(identifier)
            return 0
        command_line = options["command"]
        if "environment-lines" in command_line:
            with State() as data:
                rows = data.get("probe", {})
            for key, value in rows.items():
                print(f"{key}={value}")
            print("environment_fingerprint=unrecorded")
            return 0
        mounts = options["mounts"]
        workdir = to_host(options["workdir"], mounts)
        environment = dict(os.environ)
        environment.update({k: v for k, v in options["env"].items() if k != "PYTHONPATH"})
        environment["PYTHONPATH"] = to_host("/workspace/src", mounts)
        translated = [to_host(arg, mounts) if arg.startswith("/workspace") else arg
                      for arg in command_line]
        if translated[0] == "python3":
            translated[0] = sys.executable
        completed = subprocess.run(translated, cwd=workdir, env=environment)
        return completed.returncode
    if command == "wait":
        while True:
            with State() as data:
                container = find(data, args[-1])
                if container is None or container["status"] != "running":
                    print(container.get("exit_code", 0) if container else 0)
                    return 0
            time.sleep(0.1)
    if command == "stop":
        with State() as data:
            container = find(data, args[-1])
            if container is not None and container["status"] == "running":
                container.update({"status": "exited", "exit_code": data.get("stop_exit_code", 143),
                                  "finished_at": "2026-10-25T00:10:00.000000000Z"})
        return 0
    if command == "logs":
        with State() as data:
            container = find(data, args[-1])
        if container is None:
            print(f"Error: No such container: {args[-1]}", file=sys.stderr)
            return 1
        print("fake runner output", flush=True)
        print("fake runner error line", file=sys.stderr, flush=True)
        return 0
    if command == "rm":
        with State() as data:
            container = find(data, args[-1])
            if container is not None and container["status"] == "running":
                print("cannot remove a running container", file=sys.stderr)
                return 1
            data["containers"] = [c for c in data.get("containers", []) if c is not container]
        return 0
    print(f"fake docker: unsupported {command}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
