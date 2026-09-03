# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.recurrence.summarizer import (
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.semantics.normalize.fact_helpers import (
    get_integral_var_name,
    is_integral_expression,
)
from scripts.function_tracer_pcode.semantics.param_semantics import _get_declared_signedness
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.core.signature import is_pointer_data_type, is_void_data_type
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


class MockPointerType:
    def getLength(self):
        return 8

    def isSigned(self):
        return False

    def isPointer(self):
        return True


class MockFloatDataType:
    def getLength(self):
        return 8

    def isSigned(self):
        return True

    def isEquivalent(self, other):
        return other is self


class MockFloatDataTypeManager:
    def __init__(self, *float_types):
        self._float_types = tuple(float_types)

    def getFloatDataTypes(self):
        return self._float_types


class MockManagedFloatDataType(MockFloatDataType):
    def __init__(self):
        self._dtm = MockFloatDataTypeManager(self)

    def getDataTypeManager(self):
        return self._dtm


class MockUnsignedIntegerAlias:
    def getLength(self):
        return 4

    def isSigned(self):
        return False


class _FakeTracer:
    program = None


def test_signature_predicates_do_not_classify_string_only_runtime_types():
    assert is_pointer_data_type(None, "char *") is False
    assert is_void_data_type(None, "void") is False


def test_fact_helpers_prefer_datatype_object_over_display_name():
    expr = Expression.parameter(
        "param_1",
        index=0,
        data_type="definitely_not_float",
        data_type_obj=MockManagedFloatDataType(),
        size=8,
    )

    assert get_integral_var_name(expr) is None
    assert is_integral_expression(expr) is False


def test_recurrence_summary_uses_datatype_objects_for_pointer_and_counter_roles():
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer(), debug=False)
    analysis = create_mock_analysis(
        "loop_like",
        parameters=[
            {
                "name": "buf",
                "index": 0,
                "data_type": "not_a_pointer_name",
                "data_type_obj": MockPointerType(),
                "size": 8,
            },
            {
                "name": "count",
                "index": 1,
                "data_type": "mystery_alias",
                "data_type_obj": MockUnsignedIntegerAlias(),
                "size": 4,
            },
        ],
    )

    assert summarizer._infer_pointer_parameter_name(analysis) == "buf"
    assert summarizer._parameter_can_be_counter(analysis.parameters[1]) is True


def test_param_semantics_declared_signedness_uses_datatype_object_metadata():
    param = {
        "name": "param_1",
        "data_type": "signed_but_false_name",
        "data_type_obj": MockUnsignedIntegerAlias(),
    }

    assert _get_declared_signedness(param) == "unsigned"
