# -*- coding: utf-8 -*-
"""Concrete execution layer.

Shared foundation for establishing behavioural differences by running two
functions on corresponding concrete inputs:

* ``abi``            calling-convention models (public specification data)
* ``input_surface``  argument slots of a function, their correspondence across
                     two functions, and the register images of a value
* ``observation``    what is compared after two runs (the return register)
* ``executor``       the executor contract: entry state, request, result
* ``comparison``     what two runs establish

The layer depends on ``core`` only.  It does not read source code, expected
verdicts or the symbolic analysis, and it produces facts, never an outcome.
Submodules are imported explicitly; this package re-exports nothing.
"""
