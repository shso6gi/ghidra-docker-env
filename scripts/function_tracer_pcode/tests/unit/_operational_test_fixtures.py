# -*- coding: utf-8 -*-
"""Ghidra の Program / Function / 逆コンパイル結果と broker の最小 fake（test 専用）。

operational extraction の test と、Issue #163 の supervisor harness（実 child の
checkpoint step）が同じものを使う。どちらかの test module の private に依存
させないため、ここに置く。production の型ではなく、broker と
``OperationalExtractionAuthorityFactory`` が読む Ghidra API の形だけを持つ。
"""


class AddressSpace:
    def __init__(self, name="ram"):
        self.name = name

    def getName(self):
        return self.name


class Address:
    def __init__(self, offset, space="ram"):
        self.offset = offset
        self.space = AddressSpace(space)

    def getAddressSpace(self):
        return self.space

    def getOffset(self):
        return self.offset


class Function:
    def __init__(self, entry=0x1000, name="f", program=None):
        self.entry = Address(entry)
        self.name = name
        self.program = program

    def getEntryPoint(self):
        return self.entry

    def getName(self):
        return self.name

    def getProgram(self):
        return self.program

    def getBody(self):
        return Body(self.entry.offset, self.entry.offset + 0x20)

    def getParameters(self):
        return ()

    def getCallingConventionName(self):
        return "__cdecl"

    def getReturn(self):
        return None

    def getReturnType(self):
        return None


class Body:
    def __init__(self, minimum, maximum):
        self.minimum = Address(minimum)
        self.maximum = Address(maximum)

    def getAddressRanges(self):
        return None

    def getMinAddress(self):
        return self.minimum

    def getMaxAddress(self):
        return self.maximum


class CompilerSpec:
    def getCompilerSpecID(self):
        return "gcc"


class Program:
    def __init__(self, manager):
        self.manager = manager

    def getFunctionManager(self):
        return self.manager

    def getExecutableFormat(self):
        return "ELF"

    def getLanguageID(self):
        return "x86:LE:64:default"

    def getCompilerSpec(self):
        return CompilerSpec()

    def getImageBase(self):
        return Address(0x400000)


class Result:
    def __init__(
        self, *, completed=False, timed_out=False, failed=False,
        cancelled=False, function=None, high=None, message="",
    ):
        self.completed = completed
        self.timed_out = timed_out
        self.failed = failed
        self.cancelled = cancelled
        self.function = function
        self.high = high
        self.message = message
        self.high_call_count = 0

    def decompileCompleted(self):
        return self.completed

    def isTimedOut(self):
        return self.timed_out

    def failedToStart(self):
        return self.failed

    def isCancelled(self):
        return self.cancelled

    def getFunction(self):
        return self.function

    def getHighFunction(self):
        self.high_call_count += 1
        return self.high

    def getErrorMessage(self):
        return self.message


class BrokerDecompiler:
    def __init__(self, result):
        self.result = result
        self.calls = 0

    def decompileFunction(self, function, timeout, monitor):
        self.calls += 1
        return self.result


class BrokerAnalyzer:
    def __init__(self, program, decompiler):
        self.program = program
        self.decompiler = decompiler

    def _get_decompiler(self):
        return self.decompiler
