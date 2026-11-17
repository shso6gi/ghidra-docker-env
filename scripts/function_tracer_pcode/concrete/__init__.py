# -*- coding: utf-8 -*-
"""Concrete execution layer.

Shared foundation for establishing behavioural differences by running two
functions on corresponding concrete inputs:

* ``abi``            calling-convention models (public specification data)
* ``storage``        exact storage position of a recovered value
* ``input_surface``  argument slots of a function, their correspondence across
                     two functions, and the register images of a value
* ``observation``    what is compared after two runs (the return register)
* ``executor``       the executor contract: entry state, request, result
* ``comparison``     what two runs establish
* ``abi_conformance`` run-time check of an ABI model against the program's
                     compiler specification
* ``run_observer``   the facts of one run, derived from its execution events
* ``recording``      run traces: recording, replay without Ghidra, and the
                     recorded executor

The executor on Ghidra's P-code emulator is ``ghidra.concrete_executor``;
``ghidra.concrete_worker`` runs it in child processes.

The layer depends on ``core`` only.  It does not read source code, expected
verdicts or the symbolic analysis, and it produces facts, never an outcome.
Submodules are imported explicitly; this package re-exports nothing.
"""
