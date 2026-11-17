# -*- coding: utf-8 -*-
"""How the Ghidra executor classifies an exception that stopped a run.

The emulator's own exceptions (``ghidra.pcode.*``: an undecodable instruction,
a P-code execution error) and arithmetic exceptions are the machine semantics
stopping (``FAULT``); anything else is a failure of the executor
(``EXECUTOR_ERROR``) and never evidence about the program.  The module imports
Ghidra lazily, so this runs without it.
"""
from scripts.function_tracer_pcode.ghidra.concrete_executor import PcodeEmulatorExecutor


class _JavaError(Exception):
    def __init__(self, name, message="m"):
        super().__init__(message)
        self._name = name

    def getClass(self):
        name = self._name

        class _Class:
            def getName(self):
                return name

        return _Class()


def test_emulator_exceptions_are_faults_and_everything_else_an_executor_error():
    classify = PcodeEmulatorExecutor._classify
    assert classify(_JavaError("ghidra.pcode.exec.DecodePcodeExecutionException"))[0] == "FAULT"
    assert classify(_JavaError("ghidra.pcode.exec.PcodeExecutionException"))[0] == "FAULT"
    assert classify(_JavaError("java.lang.ArithmeticException"))[0] == "FAULT"
    assert classify(_JavaError("java.lang.NullPointerException"))[0] == "EXECUTOR_ERROR"
    assert classify(_JavaError("java.lang.OutOfMemoryError"))[0] == "EXECUTOR_ERROR"
    assert classify(ValueError("python"))[0] == "EXECUTOR_ERROR"
    termination, detail = classify(_JavaError("java.lang.ArithmeticException", "/ by zero"))
    assert "ArithmeticException" in detail and "/ by zero" in detail
