"""Bind revised final sources without relabelling original numeric evidence.

This module checks source metadata and source graphs only. Every selected
compiled output still requires authenticated restoration and the final kernel
receipt. The original 349 numerical plans and run retain their original seal.
"""
import hashlib, json, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parents[1]
BINDING = 'ci/rg_current_final_source_binding_20261103.json'
NUMERIC_SPEC = 'ci/rg_d1_required_numeric_batches_20261103.json'
NUMERIC_ORIGIN = 'ci/rg_d1_numeric_run41686621300_20261103.json'
NUMERIC_SPEC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
ENDPOINT = 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
REPOSITORY = 'RhudeJJJJ/formal-conjectures'
RUN = 41686621300
COMMIT = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
OLD_CLOSURE = '9b816edb67214c8c25a0c17e7390be126b53a03cb41bd8165c567755b5c302ac'
HEADS = {'Proofs.RadenkovicGutmanD1Long10', 'Proofs.RadenkovicGutmanD1Long30'}
REORGANIZED = 'Proofs.RadenkovicGutmanD1Long00Leaf01370'
REORGANIZED_SPEC = 'ci/rg_d1_numeric137_decomposed_20261103_spec.json'
REORGANIZED_SHA = '215ae3b2b69a4d7f9f00d694228a45333df0b73e588a6b2f0f61c97b45db4302'
INTERVAL_RECHECK = 'Proofs.RadenkovicGutmanD1OriginalSharedSlice0080Complete'
REORGANIZATION = {
    'original_module': REORGANIZED, 'original_batch': '00_137',
    'spec': REORGANIZED_SPEC, 'spec_sha256': REORGANIZED_SHA,
    'original_declarations_preserved_verbatim': True,
    'unchanged_original_numeric_modules': 4566,
    'source_reorganized_original_numeric_modules': 1,
    'added_support_modules': 11,
    'additional_final_current_source_recheck': INTERVAL_RECHECK,
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def binding_metadata(binding_raw, numeric_raw, origin_raw):
    """Validate the separate current-source and immutable numeric identities."""
    binding, numeric, origin = map(json.loads, (binding_raw, numeric_raw, origin_raw))
    assert sha(numeric_raw) == NUMERIC_SPEC_SHA
    assert numeric['kind'] == 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES'
    assert numeric['endpoint'] == ENDPOINT and numeric['required_modules'] == 33472
    assert (numeric['mathlib'], numeric['leancert'], numeric['lean_version']) == (PIN, LC, '4.33.1')
    assert numeric['source_endpoint_closure_sha256'] == OLD_CLOSURE
    assert len(numeric['jobs']) == 349
    scheduled = numeric['scheduled_numeric_modules']
    assert isinstance(scheduled, list) and len(scheduled) == len(set(scheduled)) == 4567
    assert origin['kind'] == 'PINNED_ORIGINAL_NUMERIC_RUN_FOR_FINAL_ONLY_CONTINUATION'
    assert (origin['repository'], origin['run'], origin['source_commit']) == (REPOSITORY, RUN, COMMIT)
    assert origin['numeric_spec_sha256'] == NUMERIC_SPEC_SHA and origin['numeric_jobs'] == 349
    assert origin['workflow_path'] == '.github/workflows/rg-d1-numeric-and-final-20261103.yml'
    assert origin['branch'] == 'rg-degree-one-large-20261103'
    for key in ('source_endpoint_sha256', 'source_endpoint_closure_sha256'):
        assert origin[key] == numeric[key]
    assert binding['kind'] == 'EXACT_CURRENT_FINAL_SOURCE_BINDING_NOT_KERNEL_PROOF'
    assert binding['repository'] == REPOSITORY and binding['endpoint'] == ENDPOINT
    assert (binding['mathlib'], binding['leancert'], binding['lean_version']) == (PIN, LC, '4.33.1')
    assert binding['original_numeric_spec'] == NUMERIC_SPEC
    assert binding['original_numeric_spec_sha256'] == NUMERIC_SPEC_SHA
    assert binding['original_numeric_origin'] == NUMERIC_ORIGIN
    assert binding['original_numeric_origin_sha256'] == sha(origin_raw)
    assert binding['kernel_check_required'] is True
    assert binding['complete_object_authentication_required'] is True
    assert binding['current_endpoint_source_sha256'] == numeric['source_endpoint_sha256']
    assert re.fullmatch(r'[0-9a-f]{64}', binding['current_endpoint_closure_sha256'])
    assert binding['current_endpoint_closure_sha256'] != OLD_CLOSURE
    assert binding['current_required_modules'] == 33583
    assert binding['numeric_source_reorganization'] == REORGANIZATION
    assert binding['reviewed_changed_sources']
    for name, digest in binding['reviewed_changed_sources'].items():
        assert re.fullmatch(r'Proofs\.[A-Za-z0-9_.]+', name)
        assert re.fullmatch(r'[0-9a-f]{64}', digest)
    summary = dict(kind='CURRENT_FINAL_SOURCES_WITH_EXPLICIT_NUMERIC_SOURCE_REORGANIZATION',
        binding_file=BINDING, binding_spec_sha256=sha(binding_raw),
        endpoint=ENDPOINT, required_modules=binding['current_required_modules'],
        source_endpoint_sha256=binding['current_endpoint_source_sha256'],
        source_endpoint_closure_sha256=binding['current_endpoint_closure_sha256'],
        original_numeric_run=RUN, original_numeric_source_commit=COMMIT,
        original_numeric_spec_sha256=NUMERIC_SPEC_SHA,
        original_numeric_source_endpoint_closure_sha256=OLD_CLOSURE,
        numeric_source_reorganization=REORGANIZATION,
        additional_final_current_source_rechecks=[INTERVAL_RECHECK],
        kernel_proof='NOT_ESTABLISHED_BY_SOURCE_BINDING')
    return binding, summary


def read_binding(path, numeric_raw):
    assert path.resolve() == (ROOT / BINDING).resolve(), 'Only the reviewed current binding file is accepted'
    return binding_metadata(path.read_bytes(), numeric_raw, (ROOT / NUMERIC_ORIGIN).read_bytes())


def prepare_current_sources(binding):
    """Materialize nine unchanged siblings without overwriting the split leaf."""
    assert binding['numeric_source_reorganization'] == REORGANIZATION
    import rg_numeric137_decomposed_recovery as decomposition
    current, _, expected, base, snapshot = decomposition.context(REORGANIZED_SHA)
    decomposition.preserve_declarations(current, expected, snapshot)
    decomposition.materialize_unchanged(current, expected, snapshot)
    decomposition.preserve_declarations(current, expected, snapshot)
    decomposition.source_scope(current, expected, base)


def validate_current_graph(binding, numeric, hashes, closures):
    """Keep 4,566 originals and bind the single preserved-declaration split."""
    from rg_original_d1_numeric_reproduction import load_plan
    import rg_numeric137_decomposed_recovery as decomposition

    assert binding['numeric_source_reorganization'] == REORGANIZATION
    current, original_plan, original_rows, base, snapshot = decomposition.context(REORGANIZED_SHA)
    decomposition.preserve_declarations(current, original_rows, snapshot)
    decomposition.source_scope(current, original_rows, base)

    assert set(hashes) == set(closures)
    assert len(hashes) == binding['current_required_modules']
    assert hashes[ENDPOINT] == binding['current_endpoint_source_sha256']
    assert closures[ENDPOINT] == binding['current_endpoint_closure_sha256']
    for name, digest in binding['reviewed_changed_sources'].items():
        assert hashes[name] == digest, ('Changed reviewed source', name)
    expected_names, unchanged, reorganized = set(), set(), set()
    for batch in numeric['jobs']:
        path = pathlib.PurePosixPath(batch['plan'])
        assert path.is_relative_to('ci') and '..' not in path.parts
        raw = (ROOT / path).read_bytes()
        assert sha(raw) == batch['plan_sha256'], ('Changed original numeric plan', str(path))
        plan, expected = load_plan(ROOT / path)
        assert plan['scope'] in ('original00_leaves', 'original_long_chunk')
        assert not expected_names.intersection(expected), ('Repeated numeric batch scope', batch['batch'])
        expected_names.update(expected)
        for name, row in expected.items():
            if name == REORGANIZED:
                assert batch['batch'] == '00_137' and plan == original_plan
                assert row == original_rows[name]
                assert hashes[name] == current['modules'][name]['source_sha256'] != row['source_sha256']
                assert closures[name] == current['modules'][name]['source_closure_sha256'] != row['source_closure_sha256']
                reorganized.add(name)
                continue
            assert hashes[name] == row['source_sha256'], ('Changed original numeric source', name)
            assert closures[name] == row['source_closure_sha256'], ('Changed original numeric closure', name)
            unchanged.add(name)
    assert len(expected_names) == 4567
    assert expected_names == set(numeric['scheduled_numeric_modules'])
    assert reorganized == {REORGANIZED} and len(unchanged) == 4566
    assert unchanged | reorganized == expected_names and not unchanged & reorganized
    for name in current['new_source_exports']:
        assert hashes[name] == current['modules'][name]['source_sha256']
        assert closures[name] == current['modules'][name]['source_closure_sha256']
    head_path = pathlib.PurePosixPath(numeric['head_plan'])
    assert head_path.is_relative_to('ci') and '..' not in head_path.parts
    assert sha((ROOT / head_path).read_bytes()) == numeric['head_plan_sha256']
    head_plan, heads = load_plan(ROOT / head_path)
    assert head_plan['scope'] == 'original_long_heads' and set(heads) == HEADS
    assert not expected_names.intersection(heads)
    for name, row in heads.items():
        assert hashes[name] == row['source_sha256'], ('Changed historical head source', name)
        assert closures[name] == row['source_closure_sha256'], ('Changed historical head closure', name)


def validate_contract_binding(contract, summary):
    assert contract['current_source_binding'] == {
        'path': BINDING, 'sha256': summary['binding_spec_sha256']}
    assert contract['source_endpoint_sha256'] == summary['source_endpoint_sha256']
    assert contract['source_endpoint_closure_sha256'] == summary['source_endpoint_closure_sha256']
