# ps_no_match

Issue #157 fixture. `ps` in this directory answers the first
`PS_NO_MATCH_COUNT` (default 3) calls the way procps `ps --ppid <pid>`
answers when `<pid>` has no child yet — exit 1 with empty stdout and stderr —
and then execs the real `ps` given in `PS_NO_MATCH_REAL_PS`. The number of
calls is written to the file `PS_NO_MATCH_CALLS`. Missing variables make it
exit 2 with a message on stderr.

`test_validation_result_summary.py::test_timed_command_pid_contract_survives_ps_no_match_exits`
puts it first on `PATH` for the real `/usr/bin/time` wrapper test.

## Failure before the fix (commit `15e0582`)

The pre-#157 test used `subprocess.check_output`, which turns the no-match
exit into `CalledProcessError` on the first call. From the repository root,
inside the `ghidra-dev` container (procps-ng 3.3.17, Python 3.10):

```bash
git show 15e0582:scripts/function_tracer_pcode/tests/unit/test_validation_result_summary.py \
  > scripts/function_tracer_pcode/tests/unit/test_issue157_before.py
rm -f /tmp/ps-calls
PATH="$PWD/scripts/function_tracer_pcode/tests/fixtures/ps_no_match:$PATH" \
PS_NO_MATCH_REAL_PS="$(command -v ps)" PS_NO_MATCH_CALLS=/tmp/ps-calls \
  python3 -B -m pytest scripts/function_tracer_pcode/tests/unit/test_issue157_before.py \
  -q -p no:cacheprovider -k timed_command_pid
cat /tmp/ps-calls
rm scripts/function_tracer_pcode/tests/unit/test_issue157_before.py
```

Expected: `1 failed` with
`subprocess.CalledProcessError: Command '['ps', '-o', 'pid=', '--ppid', '<pid>']' returned non-zero exit status 1.`
and `/tmp/ps-calls` = `1`. The same command against the fixed file passes
after at least 4 calls.
