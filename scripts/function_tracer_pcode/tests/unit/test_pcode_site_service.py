"""PcodeSiteService collaborator（Phase 5 #8）の回帰テスト。"""

import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import region_facts
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.pcode_sites import PcodeSiteService, varnode_location_key


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _varnode(space="register", offset=0x10, size=4):
    vn = Mock()
    vn.getAddress.return_value.getAddressSpace.return_value.getName.return_value = space
    vn.getAddress.return_value.getOffset.return_value = offset
    vn.getSize.return_value = size
    return vn


def test_collaborator_holds_only_injected_callables():
    service = _analyzer()._pcode_sites
    assert set(vars(service)) == {
        "program_access",
        "storages_overlap_for_return_recovery",
        "current_function_entry_address",
        "is_pcode_call_op",
        "get_implicit_return_target_storages",
        "binary_id_value",
    }


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(PcodeSiteService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 15
    static = {"varnode_location_key"}
    for name in names:
        sentinel = object()
        facade = inspect.getattr_static(ReturnAnalyzer, "_" + name)
        assert isinstance(facade, staticmethod) == (name in static), name
        assert not isinstance(facade, classmethod), name
        target = PcodeSiteService if name in static else analyzer._pcode_sites
        with patch.object(target, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())
            if name not in static:
                params = params[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_varnode_location_key_is_one_pure_module_function_shared_with_region_facts():
    vn = _varnode()
    assert varnode_location_key(vn) == ("register", 0x10, 4)
    assert varnode_location_key(None) is None
    assert PcodeSiteService.varnode_location_key(vn) == ("register", 0x10, 4)
    assert ReturnAnalyzer._varnode_location_key(vn) == ("register", 0x10, 4)
    assert region_facts.varnode_location_key is varnode_location_key
    assert "varnode_location_key" not in region_facts.__all__


def test_varnodes_may_alias_matches_facade_result():
    analyzer = _analyzer()
    a, b, c = _varnode(), _varnode(), _varnode(offset=0x20)
    assert analyzer._varnodes_may_alias(a, b) is True
    assert analyzer._varnodes_may_alias(a, c) is False
    assert analyzer._varnodes_may_alias(a, None) is False
    assert analyzer._pcode_sites.varnodes_may_alias(a, b) is True


def test_binary_id_supplier_reads_analyzer_state_at_call_time():
    analyzer = _analyzer()
    analyzer._binary_id = "B-late"
    assert analyzer._pcode_sites.binary_id_value() == "B-late"


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for facade_name, attr in (
        ("_storages_overlap_for_return_recovery", "storages_overlap_for_return_recovery"),
        ("_current_function_entry_address", "current_function_entry_address"),
        ("_is_pcode_call_op", "is_pcode_call_op"),
        ("_get_implicit_return_target_storages", "get_implicit_return_target_storages"),
    ):
        sentinel = object()
        with patch.object(ReturnAnalyzer, facade_name, return_value=sentinel) as mocked:
            assert getattr(analyzer._pcode_sites, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()
