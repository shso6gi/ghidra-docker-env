from scripts.function_tracer_pcode.model.call_target import CallTargetRef

import pytest


class _StoppedJvmProxy:
    def __getattr__(self, _name):
        raise RuntimeError("Java Virtual Machine is not running")


class _ProgramGetterWhoseJvmStops:
    def getProgram(self):
        return _StoppedJvmProxy()

    def __getattr__(self, _name):
        raise RuntimeError("Java Virtual Machine is not running")


class _BrokenProxy:
    def __getattr__(self, _name):
        raise RuntimeError("broken proxy")


def test_call_target_ref_tolerates_attribute_lookup_after_jvm_shutdown():
    proxy = _StoppedJvmProxy()

    target = CallTargetRef.from_function(proxy)

    assert target.kind == "function"
    assert target.function_name is None
    assert target.program_id is None
    assert target.entry_offset is None
    assert target.is_external is None
    assert target.library_name is None
    assert target.is_thunk is None
    assert target.function_obj is proxy
    assert target.analysis_key() is None


def test_call_target_ref_tolerates_program_proxy_stopping_mid_lookup():
    proxy = _ProgramGetterWhoseJvmStops()

    target = CallTargetRef.from_function(proxy)

    assert target.program_id is None
    assert target.function_name is None
    assert target.entry_offset is None
    assert target.analysis_key() is None


def test_call_target_ref_propagates_non_shutdown_proxy_error():
    with pytest.raises(RuntimeError, match="^broken proxy$"):
        CallTargetRef.from_function(_BrokenProxy())
