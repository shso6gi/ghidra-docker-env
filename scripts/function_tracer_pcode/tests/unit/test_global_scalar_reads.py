"""Issue #30: reads of global scalars are memory loads, not their addresses."""
from scripts.function_tracer_pcode.analysis.memory_resolver import concretize_readonly_loads
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.core import AddressValueRef, Expression, ExpressionType
from scripts.function_tracer_pcode.core.signature import is_composite_data_type

RODATA_ADDR = 0x100070
DOUBLE_1000 = 0x408F400000000000


class _Space:
    def getName(self):
        return "ram"

    def getSpaceID(self):
        return 1


class _Address:
    def __init__(self, offset):
        self._offset = offset

    def getOffset(self):
        return self._offset

    def getAddressSpace(self):
        return _Space()


class _Block:
    def __init__(self, writable):
        self._writable = writable

    def getName(self):
        return ".data" if self._writable else ".rodata"

    def isInitialized(self):
        return True

    def isRead(self):
        return True

    def isWrite(self):
        return self._writable

    def isExecute(self):
        return False

    def isVolatile(self):
        return False


class _ImageAddress:
    def __init__(self, offset):
        self.offset = offset

    def add(self, delta):
        return _ImageAddress(self.offset + delta)


class _Memory:
    def __init__(self, writable, image):
        self._writable = writable
        self._image = image

    def getBlock(self, _address):
        return _Block(self._writable)

    def getByte(self, address):
        return self._image[address.offset]


class _Language:
    def isBigEndian(self):
        return False


class _AddressSpace:
    def getAddress(self, offset):
        return _ImageAddress(offset)


class _AddressFactory:
    def getDefaultAddressSpace(self):
        return _AddressSpace()


def _little_endian_image(base, value, size):
    return {base + i: (value >> (8 * i)) & 0xFF for i in range(size)}


class _Program:
    def __init__(self, writable=False, image=None):
        self._writable = writable
        self._image = image if image is not None else _little_endian_image(RODATA_ADDR, DOUBLE_1000, 8)

    def getMemory(self):
        return _Memory(self._writable, self._image)

    def getLanguage(self):
        return _Language()

    def getAddressFactory(self):
        return _AddressFactory()

    def getSymbolTable(self):
        raise RuntimeError("no symbol table in this fake")

    def getUniqueProgramID(self):
        return 7

    def getDefaultPointerSize(self):
        return 8


class _DataType:
    def __init__(self, name, composite=False):
        self._name = name
        self._composite = composite
        if composite:
            self.getNumElements = lambda: 4

    def __str__(self):
        return self._name


class _Symbol:
    def __init__(self, name, data_type):
        self._name = name
        self._data_type = data_type

    def getName(self):
        return self._name

    def isParameter(self):
        return False

    def getDataType(self):
        return self._data_type

    def getAddress(self):
        return _Address(RODATA_ADDR)


class _High:
    def __init__(self, symbol):
        self._symbol = symbol

    def getSymbol(self):
        return self._symbol

    def getName(self):
        return self._symbol.getName()

    def getRepresentative(self):
        return None


class _GlobalVarnode:
    def __init__(self, symbol, size=8):
        self._symbol = symbol
        self._size = size

    def isConstant(self):
        return False

    def getDef(self):
        return None

    def getHigh(self):
        return _High(self._symbol)

    def isAddress(self):
        return True

    def isRegister(self):
        return False

    def isUnique(self):
        return False

    def isInput(self):
        return True

    def getSize(self):
        return self._size

    def getAddress(self):
        return _Address(RODATA_ADDR)

    def getOffset(self):
        return RODATA_ADDR


def _tracer(program):
    tracer = PcodeTracer(program, None, debug=False)
    tracer._get_storage_info_from_varnode = lambda _varnode: None
    return tracer


def test_is_composite_data_type_recognises_arrays_and_structs_but_not_scalars():
    assert is_composite_data_type(_DataType("double[4]", composite=True))
    assert is_composite_data_type(None, "int[16]")
    assert is_composite_data_type(None, "struct point")
    assert not is_composite_data_type(_DataType("double"))
    assert not is_composite_data_type(None, "undefined8")
    assert not is_composite_data_type(None, "double *")


def test_readonly_global_scalar_input_varnode_traces_to_its_image_constant():
    tracer = _tracer(_Program(writable=False))
    expr = tracer._trace_varnode_internal(
        _GlobalVarnode(_Symbol("DAT_00100070", _DataType("double"))), depth=0, use_cache=False
    )

    assert expr.expr_type == ExpressionType.CONSTANT
    assert expr.value == DOUBLE_1000
    assert expr.size == 8


def test_readonly_global_without_image_bytes_falls_back_to_memory_load():
    tracer = _tracer(_Program(writable=False, image={}))
    expr = tracer._trace_varnode_internal(
        _GlobalVarnode(_Symbol("DAT_00100070", _DataType("double"))), depth=0, use_cache=False
    )

    assert expr.expr_type == ExpressionType.MEMORY
    address = expr.operands[0]
    assert address.expr_type == ExpressionType.CONSTANT and address.value == RODATA_ADDR
    assert isinstance(address.runtime_ref, AddressValueRef)
    assert address.runtime_ref.is_readonly_memory()


def test_writable_global_scalar_input_varnode_traces_to_memory_load():
    tracer = _tracer(_Program(writable=True))
    expr = tracer._trace_varnode_internal(
        _GlobalVarnode(_Symbol("counter", _DataType("long"))), depth=0, use_cache=False
    )

    assert expr.expr_type == ExpressionType.MEMORY
    address = expr.operands[0]
    assert address.value == RODATA_ADDR
    assert address.runtime_ref.can_write is True


def test_global_composite_input_varnode_keeps_address_object_semantics():
    tracer = _tracer(_Program(writable=False))
    expr = tracer._trace_varnode_internal(
        _GlobalVarnode(_Symbol("table", _DataType("double[4]", composite=True)), size=32),
        depth=0, use_cache=False,
    )

    assert expr.expr_type == ExpressionType.CONSTANT
    assert expr.value == RODATA_ADDR
    assert isinstance(expr.runtime_ref, AddressValueRef)


def _load_of(runtime_ref):
    return Expression.memory(Expression.constant(RODATA_ADDR, 8, runtime_ref=runtime_ref), 8)


def _ref(**overrides):
    values = dict(
        address_offset=RODATA_ADDR, source="symbol_address", display_hint="DAT_00100070",
        program_id=7, space_id=1, space_name="ram", symbol_name="DAT_00100070",
        block_name=".rodata", is_initialized=True, can_read=True, can_write=False,
        can_execute=False, is_volatile=False,
    )
    values.update(overrides)
    return AddressValueRef(**values)


def _read(address, size):
    return DOUBLE_1000 if (address, size) == (RODATA_ADDR, 8) else None


def test_readonly_global_scalar_load_is_concretised_from_the_image():
    resolved = concretize_readonly_loads(_load_of(_ref()), [], [], _read, image_base=0x100000)

    assert resolved.expr_type == ExpressionType.CONSTANT
    assert resolved.value == DOUBLE_1000
    assert resolved.size == 8


def test_writable_or_volatile_global_load_stays_a_symbolic_memory_read():
    for ref in (_ref(block_name=".data", can_write=True), _ref(is_volatile=True)):
        resolved = concretize_readonly_loads(_load_of(ref), [], [], _read, image_base=0x100000)
        assert resolved.expr_type == ExpressionType.MEMORY
        assert resolved.operands[0].value == RODATA_ADDR


def test_end_to_end_traced_readonly_global_concretises():
    tracer = _tracer(_Program(writable=False, image={}))
    traced = tracer._trace_varnode_internal(
        _GlobalVarnode(_Symbol("DAT_00100070", _DataType("double"))), depth=0, use_cache=False
    )
    resolved = concretize_readonly_loads(traced, [], [], _read, image_base=0x100000)
    assert resolved.expr_type == ExpressionType.CONSTANT and resolved.value == DOUBLE_1000

    traced_writable = _tracer(_Program(writable=True))._trace_varnode_internal(
        _GlobalVarnode(_Symbol("counter", _DataType("long"))), depth=0, use_cache=False
    )
    resolved_writable = concretize_readonly_loads(traced_writable, [], [], _read, image_base=0x100000)
    assert resolved_writable.expr_type == ExpressionType.MEMORY
