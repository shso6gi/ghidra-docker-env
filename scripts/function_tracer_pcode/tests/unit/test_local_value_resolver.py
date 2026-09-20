"""Phase 5: LocalValueResolver is the second collaborator extracted from
ReturnAnalyzer.  It owns no analysis state; pure helpers are imported from
their owners and only the DebugReporter is injected."""
from types import SimpleNamespace

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.effect_integration import local_memory_key
from scripts.function_tracer_pcode.analysis.returns.expression_cases import clone_expression
from scripts.function_tracer_pcode.analysis.returns.local_values import LocalValueResolver
from scripts.function_tracer_pcode.core import Expression, ExpressionType
from scripts.function_tracer_pcode.tests.unit._publication import published


class _Varnode:
    def __init__(self, space, offset, size, *, constant=False, definition=None):
        self._space, self._offset, self._size = space, offset, size
        self._constant, self._definition = constant, definition

    def getAddress(self):
        return SimpleNamespace(getAddressSpace=lambda: SimpleNamespace(getName=lambda: self._space))

    def getOffset(self):
        return self._offset

    def getSize(self):
        return self._size

    def isConstant(self):
        return self._constant

    def getDef(self):
        return self._definition


class _Op:
    def __init__(self, mnemonic, inputs, output=None):
        self._mnemonic, self._inputs, self._output = mnemonic, inputs, output

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]

    def getOutput(self):
        return self._output


class _Tracer:
    def __init__(self, storages=None):
        self._storages = storages or {}
        self.traced = []

    def trace_varnode(self, varnode, use_cache=False):
        self.traced.append(varnode)
        return Expression.parameter(f"traced_{varnode.getOffset()}", 0, size=varnode.getSize())

    def _get_storage_info_from_varnode(self, varnode):
        return self._storages.get(varnode.getOffset())


class _Storage:
    def __init__(self, name, size, bit_offset=0, base="x"):
        self.register_name, self.size, self.bit_offset_in_base, self.is_register, self._base = name, size, bit_offset, True, base

    def shares_base_register_with(self, other):
        return self._base == other._base

    def bit_range_overlaps_with(self, other):
        return True


def _resolver(messages=None):
    reporter = SimpleNamespace(
        debug_available=lambda: True,
        debug_print=lambda msg, indent=0: (messages if messages is not None else []).append(msg),
    )
    return LocalValueResolver(debug_reporter=reporter)


def test_varnode_key_and_synthetic_fallback():
    resolver = _resolver()
    assert resolver.varnode_key(_Varnode("register", 0x20, 8)) == ("register", 0x20, 8)
    broken = object()
    assert resolver.varnode_key(broken) == ("synthetic", id(broken), 0)


def test_evaluate_varnode_uses_cache_constants_definitions_and_tracer():
    resolver = _resolver()
    tracer = _Tracer()
    values, storages, memory = {}, {}, {}
    # cached value wins
    cached = Expression.constant(7, 4)
    values[("register", 0x20, 8)] = cached
    assert resolver.evaluate_varnode(_Varnode("register", 0x20, 8), tracer, values, storages, memory) is cached
    # constants
    const = resolver.evaluate_varnode(_Varnode("const", 5, 4, constant=True), tracer, values, storages, memory)
    assert const.expr_type == ExpressionType.CONSTANT and const.value == 5
    # definition: out = in0 + in1 evaluates through the p-code op and is cached
    a = _Varnode("register", 0x28, 4, constant=True); b = _Varnode("const", 3, 4, constant=True)
    out = _Varnode("unique", 0x100, 4, definition=_Op("INT_ADD", [a, b], output=_Varnode("unique", 0x100, 4)))
    expr = resolver.evaluate_varnode(out, tracer, values, storages, memory)
    assert expr.operator == "INT_ADD" and values[("unique", 0x100, 4)] is expr
    # no definition, no alias: falls back to the tracer
    fallback = resolver.evaluate_varnode(_Varnode("register", 0x30, 8), tracer, values, storages, memory)
    assert fallback.name == "traced_48" and tracer.traced
    # None
    assert resolver.evaluate_varnode(None, tracer, values, storages, memory).expr_type == ExpressionType.UNKNOWN


def test_evaluate_pcode_copy_load_and_memory_cache():
    resolver = _resolver()
    tracer = _Tracer(); values, storages, memory = {}, {}, {}
    src = _Varnode("const", 9, 4, constant=True)
    copied = resolver.evaluate_pcode(_Op("COPY", [src], output=_Varnode("unique", 1, 8)), tracer, values, storages, memory)
    assert copied.value == 9 and copied.size == 8          # cloned, resized to the output
    addr = _Varnode("const", 0x1000, 8, constant=True)
    load = resolver.evaluate_pcode(_Op("LOAD", [_Varnode("const", 0, 4, constant=True), addr], output=_Varnode("unique", 2, 4)), tracer, values, storages, memory)
    assert load.expr_type == ExpressionType.MEMORY
    # a prior store to the same location is served from the memory table
    stored = Expression.constant(42, 4)
    memory[local_memory_key(Expression.constant(0x1000, 8), 4)] = stored
    assert resolver.evaluate_pcode(_Op("LOAD", [_Varnode("const", 0, 4, constant=True), addr], output=_Varnode("unique", 3, 4)), tracer, values, storages, memory) is stored
    assert resolver.evaluate_pcode(_Op("CALLOTHER", [src]), tracer, values, storages, memory) is None


def test_lookup_alias_and_for_storage_report_through_injected_debug_print():
    messages = []
    resolver = _resolver(messages)
    full = _Storage("x0", 8); low = _Storage("w0", 4)
    tracer = _Tracer(storages={0x20: low})
    values = {("register", 0x20, 8): Expression.parameter("p", 0, size=8)}
    storages = {("register", 0x20, 8): full}
    aliased = resolver.lookup_alias(_Varnode("register", 0x20, 4), tracer, values, storages)
    assert aliased is not None and aliased.size == 4 and aliased is not values[("register", 0x20, 8)]
    assert messages and messages[0].startswith("Local alias resolution")
    best = resolver.lookup_for_storage(low, values, storages)
    assert best is not None and best.size == 4
    assert resolver.lookup_for_storage(None, values, storages) is None


def test_pure_helpers_and_facade_delegation():
    expr = Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, 4))
    copy = clone_expression(expr)
    assert copy is not expr and copy.operands[0] is not expr.operands[0] and published(copy).to_smt() == published(expr).to_smt()

    analyzer = ReturnAnalyzer(program=None)
    assert isinstance(analyzer._local_values, LocalValueResolver)
    assert analyzer._local_varnode_key(_Varnode("register", 0x20, 8)) == ("register", 0x20, 8)
    assert published(analyzer._clone_expression(expr)).to_smt() == published(expr).to_smt()
    assert analyzer._local_memory_key(Expression.constant(0x1000, 8), 4) == local_memory_key(Expression.constant(0x1000, 8), 4)
    tracer = _Tracer()
    fallback = analyzer._evaluate_local_varnode_expression(_Varnode("register", 0x30, 8), tracer, {}, {}, {})
    assert fallback.name == "traced_48"
