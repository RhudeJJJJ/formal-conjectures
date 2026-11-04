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
REORGANIZED166 = {f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in range(1666, 1670)}
REORGANIZED166_SPEC = 'ci/rg_d1_numeric166_decomposed_20261104_spec.json'
REORGANIZED166_SHA = '0ddb0d67758c7627ddc7fae947a7100bcb94c9ea6b26ab3f9c13fef33f7d8f8c'
INTERVAL_RECHECK166 = 'Proofs.RadenkovicGutmanD1OriginalSharedSlice0098Complete'
INTERVAL_RECHECKS = {INTERVAL_RECHECK, INTERVAL_RECHECK166}
REORGANIZATIONS = [{
    'original_modules': [REORGANIZED], 'original_batch': '00_137',
    'spec': REORGANIZED_SPEC, 'spec_sha256': REORGANIZED_SHA,
    'original_declarations_preserved_verbatim': True,
    'added_support_modules': 11,
    'additional_final_current_source_rechecks': [INTERVAL_RECHECK],
}, {
    'original_modules': sorted(REORGANIZED166), 'original_batch': '00_166',
    'spec': REORGANIZED166_SPEC, 'spec_sha256': REORGANIZED166_SHA,
    'original_declarations_preserved_verbatim': True,
    'added_support_modules': 76,
    'additional_final_current_source_rechecks': [INTERVAL_RECHECK166],
}]


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
    assert binding['current_required_modules'] == 33659
    assert binding['numeric_source_reorganizations'] == REORGANIZATIONS
    assert 'numeric_source_reorganization' not in binding
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
        numeric_source_reorganizations=REORGANIZATIONS,
        unchanged_original_numeric_modules=4562,
        source_reorganized_original_numeric_modules=5,
        added_numeric_support_modules=87,
        additional_final_current_source_rechecks=sorted(INTERVAL_RECHECKS),
        kernel_proof='NOT_ESTABLISHED_BY_SOURCE_BINDING')
    return binding, summary


def read_binding(path, numeric_raw):
    assert path.resolve() == (ROOT / BINDING).resolve(), 'Only the reviewed current binding file is accepted'
    return binding_metadata(path.read_bytes(), numeric_raw, (ROOT / NUMERIC_ORIGIN).read_bytes())


def decomposition_contexts(binding, materialize=False):
    """Use the two fixed declaration-preserving splits, never a scope override."""
    assert binding['numeric_source_reorganizations'] == REORGANIZATIONS
    import rg_numeric137_decomposed_recovery as d137
    import rg_numeric166_decomposed_recovery as d166
    s137, p137, e137, b137, snap137 = d137.context(REORGANIZED_SHA)
    s166, p166, e166, b166, partial166, snap166 = d166.context(REORGANIZED166_SHA)
    d137.preserve_declarations(s137, e137, snap137)
    d166.preserve_declarations(s166, e166, snap166)
    if materialize:
        # Reproduce only unchanged siblings. Generic chunk materialization must
        # never overwrite one of the five explicitly split public endpoints.
        d137.materialize_unchanged(s137, e137, snap137)
        d166.materialize_unchanged(s166, e166, snap166)
        d137.preserve_declarations(s137, e137, snap137)
        d166.preserve_declarations(s166, e166, snap166)
    d137.source_scope(s137, e137, b137)
    d166.source_scope(s166, e166, b166, partial166)
    return [dict(batch='00_137', current=s137, plan=p137, original=e137,
                 reorganized={REORGANIZED}),
            dict(batch='00_166', current=s166, plan=p166, original=e166,
                 reorganized=REORGANIZED166)]


def prepare_current_sources(binding):
    """Materialize both fixed batches without replacing their split leaves."""
    decomposition_contexts(binding, materialize=True)


def validate_current_graph(binding, numeric, hashes, closures):
    """Keep 4,562 originals and bind exactly five preserved-declaration splits."""
    from rg_original_d1_numeric_reproduction import load_plan
    contexts = decomposition_contexts(binding)
    by_module = {name: context for context in contexts for name in context['reorganized']}
    assert set(by_module) == {REORGANIZED} | REORGANIZED166

    assert set(hashes) == set(closures)
    assert len(hashes) == binding['current_required_modules']
    assert hashes[ENDPOINT] == binding['current_endpoint_source_sha256']
    assert closures[ENDPOINT] == binding['current_endpoint_closure_sha256']
    for name, digest in binding['reviewed_changed_sources'].items():
        assert hashes[name] == digest, ('Changed reviewed source', name)
    expected_names, unchanged, reorganized, plan_digests = set(), set(), set(), {}
    for batch in numeric['jobs']:
        path = pathlib.PurePosixPath(batch['plan'])
        assert path.is_relative_to('ci') and '..' not in path.parts
        raw = (ROOT / path).read_bytes()
        assert sha(raw) == batch['plan_sha256'], ('Changed original numeric plan', str(path))
        plan_digests[str(path)] = sha(raw)
        plan, expected = load_plan(ROOT / path)
        assert plan['scope'] in ('original00_leaves', 'original_long_chunk')
        assert not expected_names.intersection(expected), ('Repeated numeric batch scope', batch['batch'])
        expected_names.update(expected)
        for name, row in expected.items():
            if name in by_module:
                context = by_module[name]
                current = context['current']
                assert batch['batch'] == context['batch'] and plan == context['plan']
                assert row == context['original'][name]
                assert hashes[name] == current['modules'][name]['source_sha256'] != row['source_sha256']
                assert closures[name] == current['modules'][name]['source_closure_sha256'] != row['source_closure_sha256']
                reorganized.add(name)
                continue
            assert hashes[name] == row['source_sha256'], ('Changed original numeric source', name)
            assert closures[name] == row['source_closure_sha256'], ('Changed original numeric closure', name)
            unchanged.add(name)
    assert len(expected_names) == 4567
    assert expected_names == set(numeric['scheduled_numeric_modules'])
    assert reorganized == {REORGANIZED} | REORGANIZED166 and len(unchanged) == 4562
    assert unchanged | reorganized == expected_names and not unchanged & reorganized
    support = set()
    for context in contexts:
        current = context['current']
        for name in current['new_source_exports']:
            assert hashes[name] == current['modules'][name]['source_sha256']
            assert closures[name] == current['modules'][name]['source_closure_sha256']
        support.update(set(current['new_source_exports']) - context['reorganized'])
    assert len(support) == 87 and not support.intersection(expected_names)
    head_path = pathlib.PurePosixPath(numeric['head_plan'])
    assert head_path.is_relative_to('ci') and '..' not in head_path.parts
    assert sha((ROOT / head_path).read_bytes()) == numeric['head_plan_sha256']
    head_plan, heads = load_plan(ROOT / head_path)
    assert head_plan['scope'] == 'original_long_heads' and set(heads) == HEADS
    assert not expected_names.intersection(heads)
    for name, row in heads.items():
        assert hashes[name] == row['source_sha256'], ('Changed historical head source', name)
        assert closures[name] == row['source_closure_sha256'], ('Changed historical head closure', name)
    return dict(original_numeric_modules_accounted_for=len(expected_names),
        unchanged_original_numeric_modules=len(unchanged),
        source_reorganized_original_numeric_modules=sorted(reorganized),
        added_numeric_support_modules=sorted(support),
        original_numeric_batch_plans_unchanged=len(numeric['jobs']),
        fully_unchanged_original_numeric_batches=len(numeric['jobs']) - len(contexts),
        unchanged_original_long_heads=sorted(heads), original_numeric_plan_sha256=plan_digests)


def validate_contract_binding(contract, summary):
    assert contract['current_source_binding'] == {
        'path': BINDING, 'sha256': summary['binding_spec_sha256']}
    assert contract['source_endpoint_sha256'] == summary['source_endpoint_sha256']
    assert contract['source_endpoint_closure_sha256'] == summary['source_endpoint_closure_sha256']
