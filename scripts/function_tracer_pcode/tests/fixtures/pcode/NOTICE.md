# Attribution for the recorded P-code fixtures

The fixtures in this directory are derived from the **EqBench** benchmark suite.

- Upstream: <https://github.com/shrBadihi/EqBench>
- Pinned commit: `3724fce5b287cc63165028444daf904f25b0158b`
- Licence: MIT (full text below, copied from the upstream `LICENSE.md` at that
  commit)

## What the fixtures contain

Each `<case>/left.json` / `<case>/right.json` is a recording of what Ghidra
12.0.1 returned while this repository's equivalence checker analysed **one**
compiled function. The binaries themselves are produced from EqBench's C
sources by this repository's `scripts/eqbench/compile_all_arm_mips.sh`; the
`header.binary` block of every fixture names the source path, the SHA-256 and
the size of the binary it was recorded from.

Concretely, a fixture holds:

- the decompiler's intermediate representation of the recorded function and of
  every callee the analysis reached (P-code operations, varnodes, basic blocks,
  high variables, function prototypes and calling conventions), as Ghidra
  returned it;
- the read-only data bytes the analysis actually read out of the binary's
  memory image (constants and literal pools reachable from those functions);
- the results of the program, listing, symbol-table and data-type queries the
  analysis made.

That is a derivative of EqBench's C sources by way of compilation and
decompilation, which is why the attribution above is required.

**The fixtures do not contain the binaries themselves**, and nothing here can
be linked or executed. They are read back only by
`tests/unit/test_recorded_pairs.py` and
`tests/unit/test_recorded_program_roundtrip.py`, which replay the recorded
observations instead of running Ghidra.

`targets/EqBench` (the canonical read-only checkout) is git-ignored and is not
modified by recording; see `README.md` for how to make the writable working
copy the recorder reads binaries from.

## EqBench licence (MIT)

```
Copyright (c) 2021-, Sahar Badihi, The University of British Columbia, and a number of other of contributors

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
