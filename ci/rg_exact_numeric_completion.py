"""Authenticate the narrowly sealed numeric completions with mixed origins.

The old batch plans retain all ten original endpoint names. A remainder keeps
its already checked objects in their original failed-job archive. The single
declaration-preserving split has twelve explicitly current source exports and
nine unchanged historical objects. Neither case can supply an arbitrary scope.
"""
import hashlib, io, json, pathlib, re, zipfile

from module_outputs import output_members
from rg_github_artifacts import fetch_archive

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PARTIAL = 'ORIGINAL_PARTIAL_PRIORS_WITH_FRESH_REMAINDER'
REORGANIZED = 'DECLARATION_PRESERVING_ORIGINAL137_FULL_BATCH'
ZERO_AUDIT = 'NUMERIC137_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT'
SPEC137 = 'ci/rg_d1_numeric137_decomposed_20261103_spec.json'
SHA137 = '215ae3b2b69a4d7f9f00d694228a45333df0b73e588a6b2f0f61c97b45db4302'
REMAINDERS = {
    '00_139': '18a46b10ebaff7640f068ae35001eafdba401c90265cbf1634fa0221a9fed922',
    '00_156': '23cd16f29c7ed1501e973a64ae9696f48c8eede0d26b638fadb3d080e175707c',
    '00_164': '0be737163dbafd7901cc7096e45e2113ddc2eb4caf5245e880e75f98577140e2',
    '00_166': 'd8aeaa83a3ff9496203b2b2c442a66589a3f907b154643a677a8281f871c60a5',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def identity(name, row):
    return (row['source_sha256'], row['source_closure_sha256'], row['output_sha256'],
            row['axiom_profiles'], tuple(sorted(output_members(name, row))))


def completion_context(item):
    """Only reviewed fixed specs may describe a non-flat whole-batch recovery."""
    kind = item['completion_kind']
    if kind == ZERO_AUDIT:
        from rg_numeric137_zero_fresh_completion import completion_context as zero_context
        return zero_context(item)
    if kind == PARTIAL:
        from rg_d1_numeric_remainder import load_remainder, PARTIALS
        batch = item['batch']
        assert batch in REMAINDERS
        relative = 'ci/rg_d1_numeric_remainder_20261103/batch' + batch + '.json'
        assert item['completion_spec'] == {'path': relative, 'sha256': REMAINDERS[batch]}
        assert sha((ROOT / relative).read_bytes()) == REMAINDERS[batch]
        spec, plan, expected, partial = load_remainder(batch)
        assert item['original_job'] == PARTIALS[batch]['job']
        assert item['original_plan_sha256'] == spec['original_plan_sha256']
        assert item['job_name'] == 'Complete original numeric remainder ' + batch
        assert item['required_success_step'] == 'Require exact historical output identities'
        if 'workflow_path' in item:
            expected_workflow = ('.github/workflows/rg-d1-numeric139-partial-remainder-20261103.yml'
                if batch == '00_139' else '.github/workflows/rg-d1-numeric166-partial-remainder-20261104.yml'
                if batch == '00_166' else '.github/workflows/rg-d1-numeric-partial-remainders-20261103.yml')
            assert item['workflow_path'] == expected_workflow
        return dict(kind=kind, spec=spec, plan=plan, original=expected,
                    expected={n: expected[n] for n in spec['fresh_modules']},
                    prior=partial, new_sources=set())
    assert kind == REORGANIZED
    import rg_numeric137_decomposed_recovery as decomposition
    assert item['batch'] == '00_137'
    assert item['completion_spec'] == {'path': SPEC137, 'sha256': SHA137}
    spec, plan, expected, base, snapshot = decomposition.context(SHA137)
    assert item['original_plan_sha256'] == spec['original_plan_sha256']
    assert item['original_job'] == 126095228986
    assert item['job_name'] == 'Check complete numeric00_137 with original declarations in bounded modules'
    assert item['required_success_step'] == 'Authenticate current exports and the nine unchanged historical objects'
    if 'workflow_path' in item:
        assert item['workflow_path'] == '.github/workflows/rg-d1-numeric137-decomposed-recovery-20261103.yml'
    decomposition.preserve_declarations(spec, expected, snapshot)
    current = {n: spec['modules'][n] if n in decomposition.NEW else expected[n]
               for n in spec['modules']}
    assert len(current) == 21 and len(decomposition.NEW) == 12
    return dict(kind=kind, spec=spec, plan=plan, original=expected,
                expected=current, prior=None, new_sources=set(decomposition.NEW), base=base,
                original_snapshot=snapshot)


def compare_completion_records(context, fresh, hashes, closures):
    expected, new_sources = context['expected'], context['new_sources']
    assert set(fresh) == set(expected), ('Changed exact completion frontier', set(fresh) ^ set(expected))
    for name, row in fresh.items():
        old = expected[name]
        assert row['module'] == name and row['mode'] == 'FRESH_KERNEL_EXPORT'
        assert row['source_sha256'] == hashes[name] == old['source_sha256']
        assert row['source_closure_sha256'] == closures[name] == old['source_closure_sha256']
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        list(output_members(name, row))
        if name in new_sources:
            # The original verifier grouped empty profiles at the end. Exact
            # named logs, checked below, supply their current association.
            assert 'axiom_profiles' not in old
            assert len(row['axiom_profiles']) == old['axiom_profile_count']
        else:
            assert row['axiom_profiles'] == old['axiom_profiles']
            assert identity(name, row) == identity(name, old), ('Changed historical object', name)


def open_archive(manifest):
    raw = fetch_archive(manifest)
    assert len(raw) <= 1024**3
    assert sha(raw) == manifest['artifact_sha256']
    archive = zipfile.ZipFile(io.BytesIO(raw))
    names = archive.namelist()
    assert len(names) == len(set(names)) <= 4096
    for name in names:
        path = pathlib.PurePosixPath(name)
        assert not path.is_absolute() and '..' not in path.parts
    return archive


def module_log(archive, name, row):
    raw = archive.read(name + '.log')
    assert len(raw) <= 32 * 1024**2
    text = raw.decode('utf-8')
    assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', text)
    profiles = [sorted(set(x.strip() for x in p.split(',') if x.strip()))
                for p in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text)]
    profiles += [[] for _ in re.findall('does not depend on any axioms', text)]
    assert profiles == row['axiom_profiles'], ('Changed actual module-log profiles', name)


def archived_fresh(archive, fresh):
    names = {p[:-5] for p in archive.namelist() if p.startswith('Proofs.') and p.endswith('.json')}
    assert names == set(fresh), ('Unexpected archived fresh module set', names ^ set(fresh))
    for name, row in fresh.items():
        assert json.loads(archive.read(name + '.json')) == row
        module_log(archive, name, row)


def authenticate_completion(item, artifact, context, fresh, hashes, closures, repository, api=None):
    """Read both actual archives before accepting a two-origin full batch."""
    if context['kind'] == ZERO_AUDIT:
        from rg_numeric137_zero_fresh_completion import authenticate_completion as zero_audit
        assert api is not None and repository == 'RhudeJJJJ/formal-conjectures'
        return zero_audit(item, artifact, context, fresh, hashes, closures, api)
    manifest = dict(repository=repository, run=item['run'], job=item['job'],
        source_commit=item['source_commit'], artifact_id=artifact['id'],
        artifact_sha256=artifact['digest'].removeprefix('sha256:'))
    assert artifact['size_in_bytes'] <= 1024**3
    with open_archive(manifest) as current:
        archived_fresh(current, fresh)
        receipt_raw = current.read('receipt.json')
        assert len(receipt_raw) <= 32 * 1024**2
        if context['kind'] == PARTIAL:
            return authenticate_remainder(item, context, current, receipt_raw, hashes, closures)
        return authenticate_reorganization(context, current, receipt_raw, fresh, hashes, closures)


def authenticate_remainder(item, context, current, receipt_raw, hashes, closures):
    from rg_d1_numeric_remainder import complete_receipt, partial_origin, bound
    spec, plan, expected, partial = (context[k] for k in ('spec', 'plan', 'original', 'prior'))
    from rg_plan_exact_degree_one_large import source_closure
    required = set()
    for endpoint in plan['endpoints']:
        required.update(source_closure(endpoint)[0])
    assert len(required) == 84
    scope_hashes = {n: hashes[n] for n in required}
    scope_closures = {n: closures[n] for n in required}
    diagnostics = json.loads(current.read('diagnostics_records.json'))['modules']
    archived_records = {r['module']: r for r in diagnostics}
    assert len(archived_records) == len(diagnostics)
    receipt_records = json.loads(receipt_raw)['modules']
    assert set(receipt_records) <= set(archived_records)
    assert all(archived_records[n] == r for n, r in receipt_records.items())
    with open_archive(partial) as old:
        assert 'receipt.json' not in old.namelist()
        archived_fresh(old, partial['modules'])
        member_archives = {}
        for name in expected:
            row = partial['modules'][name] if name in partial['modules'] else context['expected'][name]
            archive = old if name in partial['modules'] else current
            for relative, _, _ in output_members(name, row):
                assert relative not in member_archives
                member_archives[relative] = archive
        def read_record(relative):
            name = relative.removesuffix('.json')
            assert relative == name + '.json' and name in expected
            if name not in partial['modules']:
                return current.read(relative)
            # The successful archive retains the actual restored PRIOR record
            # in diagnostics_records; complete_receipt checks its full old
            # archive origin and historical identity without relabelling it.
            return json.dumps(archived_records[name]).encode()
        receipt, logical = complete_receipt(spec, plan, expected, partial, scope_hashes, scope_closures,
            receipt_raw, read_record,
            lambda p: member_archives[p].open(p),
            lambda p: member_archives[p].getinfo(p).file_size)
    base = bound(plan['base_manifest'], plan['base_manifest_sha256'])
    for name in required - set(expected):
        assert receipt['modules'][name]['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
        assert identity(name, receipt['modules'][name]) == identity(name, base['modules'][name])
    report = json.loads(current.read('original_numeric_complete_recovery.json'))
    assert report['status'] == 'COMPLETE_ORIGINAL_NUMERIC_BATCH_VERIFIED_WITH_PRESERVED_PARTIAL_ORIGINS'
    assert report['batch'] == item['batch'] and report['required_modules'] == 84
    assert report['source_commit'] == item['source_commit'] and report['workflow_run'] == item['run']
    assert report['workflow_attempt'] == item['actual_run_attempt']
    assert report['receipt_sha256'] == sha(receipt_raw)
    assert report['original_endpoints'] == plan['endpoints']
    assert report['original_plan'] == spec['original_plan']
    assert report['original_plan_sha256'] == spec['original_plan_sha256']
    assert report['prior_original_modules'] == sorted(partial['modules'])
    assert report['fresh_modules'] == spec['fresh_modules']
    assert report['partial_original_origin'] == partial_origin(partial)
    assert report['partial_manifest_sha256'] == spec['partial_manifest_sha256']
    assert report['all_ten_original_output_identities_verified'] is True
    assert report['verified_output_bytes'] == logical
    assert report['old_failed_job_status'] == 'UNCHANGED_FAILURE'
    assert report['prior_records_relabelled_as_fresh'] is False
    return partial['modules'], dict(kind=PARTIAL, required_modules=84, original_endpoints=10,
        fresh_exports=len(context['expected']), preserved_original_exports=len(partial['modules']),
        receipt_sha256=sha(receipt_raw), authenticated_original_partial_origin=partial_origin(partial),
        original_partial_manifest=spec['partial_manifest'], original_partial_manifest_sha256=spec['partial_manifest_sha256'],
        actual_output_bytes_verified=logical, prior_records_relabelled_as_fresh=False)


def authenticate_reorganization(context, archive, receipt_raw, fresh, hashes, closures):
    spec, expected, base = context['spec'], context['original'], context['base']
    receipt = json.loads(receipt_raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == spec['endpoints']
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC and 'version 4.33.1,' in receipt['lean']
    assert set(receipt['modules']) == set(spec['required_modules']) and len(receipt['modules']) == 95
    assert {n for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'} == set(fresh)
    logical = 0
    for name, row in receipt['modules'].items():
        assert row['module'] == name
        assert row['source_sha256'] == hashes[name] == spec['required_source_sha256'][name]
        assert row['source_closure_sha256'] == closures[name] == spec['required_source_closure_sha256'][name]
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        if name not in fresh:
            assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            assert identity(name, row) == identity(name, base['modules'][name])
            continue
        assert row == fresh[name]
        if name not in context['new_sources']:
            assert identity(name, row) == identity(name, expected[name])
        for relative, digest, size in output_members(name, row):
            actual_size = archive.getinfo(relative).file_size
            assert size is None or size == actual_size
            with archive.open(relative) as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
            logical += actual_size
    assert logical <= 8 * 1024**3
    from rg_numeric137_decomposed_recovery import validate_named_split_axioms
    named_audit = validate_named_split_axioms(spec, expected, context['original_snapshot'],
        receipt['modules'], lambda name: archive.read(name + '.log'))
    assert json.loads(archive.read('numeric137_decomposed_named_axioms.json')) == named_audit
    report = json.loads(archive.read('numeric137_decomposed_verified.json'))
    assert report['status'] == 'COMPLETE_ORIGINAL_BATCH_WITH_DECLARATION_PRESERVING_SPLIT_KERNEL_VERIFIED'
    assert report['original_plan_sha256'] == spec['original_plan_sha256']
    assert report['current_spec_sha256'] == SHA137 and report['original_endpoints'] == spec['endpoints']
    assert (report['required_modules'], report['prior_modules'], report['fresh_modules']) == (95, 74, 21)
    assert report['unchanged_historical_numeric_objects_reproduced'] == 9
    assert report['source_reorganized_original_numeric_modules'] == spec['source_reorganized_original_modules']
    assert report['added_support_modules'] == 11
    assert report['original_declarations_preserved_verbatim'] is True and report['proof_bodies_changed'] is False
    assert report['standard_axioms_only'] is True and report['verified_fresh_output_bytes'] == logical
    assert report['named_axiom_profiles_verified'] is True
    assert report['complete_original_axiom_profile_array_preserved'] is True
    assert report['historical_normalized_profile_sha256'] == named_audit['historical_normalized_profile_sha256']
    return {}, dict(kind=REORGANIZED, required_modules=95, original_endpoints=10,
        fresh_exports=21, unchanged_historical_numeric_objects=9,
        current_source_exports=sorted(context['new_sources']), receipt_sha256=sha(receipt_raw),
        named_original_declarations_verified=313,
        historical_normalized_profile_sha256=named_audit['historical_normalized_profile_sha256'],
        original_declarations_preserved_verbatim=True, actual_output_bytes_verified=logical)
