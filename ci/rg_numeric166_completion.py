"""Authenticate numeric166's four kernel origins and zero-fresh batch join.

The successful join is evidence for assembling the ten original endpoints.
Compiled objects retain their four actual leaf-job origins and the six objects
from the old failed original batch. No joined object is reexported as fresh.
"""
import hashlib
import io
import json
import pathlib
import re
import tempfile
import zipfile

import rg_numeric166_decomposed_recovery as decomposition
from rg_github_artifacts import fetch_archive
from module_outputs import output_members

ROOT = pathlib.Path(__file__).resolve().parents[1]
KIND = 'NUMERIC166_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_BATCH_JOIN'
SPEC_SHA = '0ddb0d67758c7627ddc7fae947a7100bcb94c9ea6b26ab3f9c13fef33f7d8f8c'
JOB_NAME = 'Join complete original numeric166 batch'
SUCCESS_STEP = 'Require full original batch and all preserved origins'
DESCRIPTOR_KEYS = {'repository', 'run', 'job', 'source_commit', 'artifact_id',
                   'artifact_sha256', 'artifact_name'}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def completion_context(item):
    required = {'batch', 'original_job', 'original_plan_sha256', 'run', 'job',
        'source_commit', 'artifact_id', 'artifact_sha256', 'artifact_name', 'job_name',
        'required_success_step', 'completion_kind', 'completion_spec', 'compiled_leaf_origins'}
    optional = {'workflow_path', 'key', 'actual_run_attempt', 'numeric_replacement',
                'original_manifests', 'fresh_module_origins'}
    assert required <= set(item) <= required | optional
    assert item['completion_kind'] == KIND and item['batch'] == '00_166'
    assert item['original_job'] == 126095241107
    assert item['completion_spec'] == {'path': decomposition.SPEC, 'sha256': SPEC_SHA}
    spec, plan, original, base, partial, snapshots = decomposition.context(SPEC_SHA)
    decomposition.preserve_declarations(spec, original, snapshots)
    assert item['original_plan_sha256'] == spec['original_plan_sha256']
    assert item['job_name'] == JOB_NAME and item['required_success_step'] == SUCCESS_STEP
    if 'workflow_path' in item:
        assert item['workflow_path'] == decomposition.WORKFLOW
    if 'key' in item:
        assert item['key'] == 'batch00_166'
    for name in ('original_manifests', 'fresh_module_origins'):
        if name in item:
            assert item[name] == plan[name]
    for name in ('run', 'job', 'artifact_id'):
        assert type(item[name]) is int and item[name] > 0
    assert item['run'] != 41686621300 and item['job'] != item['original_job']
    assert re.fullmatch(r'[0-9a-f]{40}', item['source_commit'])
    assert item['source_commit'] != spec['original_master_source_commit']
    assert re.fullmatch(r'[0-9a-f]{64}', item['artifact_sha256'])
    assert re.fullmatch(r'rg-d1-numeric166-complete-' + str(item['run']) + r'-[1-9][0-9]*',
                        item['artifact_name'])
    origins = item['compiled_leaf_origins']
    assert set(origins) == set(decomposition.KEYS)
    jobs, artifacts = {item['job']}, {item['artifact_id']}
    for key, origin in origins.items():
        assert set(origin) == DESCRIPTOR_KEYS
        assert origin['repository'] == decomposition.REPOSITORY
        assert origin['run'] == item['run'] and origin['source_commit'] == item['source_commit']
        for name, used in (('job', jobs), ('artifact_id', artifacts)):
            assert type(origin[name]) is int and origin[name] > 0 and origin[name] not in used
            used.add(origin[name])
        assert re.fullmatch(r'[0-9a-f]{64}', origin['artifact_sha256'])
        assert re.fullmatch(r'rg-d1-numeric166-leaf-' + key + '-' + str(item['run']) +
                            r'-[1-9][0-9]*', origin['artifact_name'])
    return dict(kind=KIND, spec=spec, plan=plan, original=original, base=base,
        partial=partial, snapshots=snapshots, expected={}, prior=partial,
        new_sources=set(decomposition.NEW))


def checked_job(api, origin, name, step, attempt=None):
    job = api.get('/actions/jobs/' + str(origin['job']))
    assert job['id'] == origin['job'] and job['run_id'] == origin['run']
    assert job['head_sha'] == origin['source_commit'] and job['name'] == name
    assert job['head_branch'] == 'rg-degree-one-large-20261103'
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert type(job['run_attempt']) is int and job['run_attempt'] > 0
    if attempt is not None:
        assert job['run_attempt'] == attempt
    steps = [s for s in job['steps'] if s['name'] == step]
    assert len(steps) == 1 and steps[0]['status'] == 'completed' and steps[0]['conclusion'] == 'success'
    return job


def checked_artifact(artifact, origin, maximum):
    assert artifact['id'] == origin['artifact_id'] and artifact['name'] == origin['artifact_name']
    assert artifact['digest'] == 'sha256:' + origin['artifact_sha256'] and not artifact['expired']
    assert artifact['workflow_run']['id'] == origin['run']
    assert artifact['workflow_run']['head_sha'] == origin['source_commit']
    assert artifact['workflow_run']['head_branch'] == 'rg-degree-one-large-20261103'
    assert type(artifact['size_in_bytes']) is int and 0 < artifact['size_in_bytes'] <= maximum


def small_archive(raw, digest):
    assert len(raw) <= 32 * 1024**2 and sha(raw) == digest
    archive = zipfile.ZipFile(io.BytesIO(raw))
    names = archive.namelist()
    assert len(names) == len(set(names)) <= 512
    for info in archive.infolist():
        path = pathlib.PurePosixPath(info.filename)
        assert not path.is_absolute() and '..' not in path.parts
        assert (info.external_attr >> 16) & 0o170000 != 0o120000
        assert info.file_size <= 32 * 1024**2
    return archive


def authenticate_partial(api, partial, original):
    from rg_exact_numeric_completion import open_archive, archived_fresh
    old = api.get('/actions/jobs/' + str(partial['job']))
    assert old['id'] == 126095241107 and old['run_id'] == 41686621300
    assert old['head_sha'] == partial['source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert old['name'] == 'original-numeric-00_166'
    assert old['run_attempt'] == 1 and old['head_branch'] == 'rg-degree-one-large-20261103'
    assert old['status'] == 'completed' and old['conclusion'] in ('failure', 'timed_out')
    metadata = api.get('/actions/artifacts/' + str(partial['artifact_id']))
    assert metadata['id'] == partial['artifact_id'] and not metadata['expired']
    assert metadata['name'] == partial['origin_context']['artifact_name']
    assert metadata['workflow_run']['id'] == partial['run'] == old['run_id']
    assert metadata['workflow_run']['head_sha'] == partial['source_commit']
    assert metadata['digest'] == 'sha256:' + partial['artifact_sha256']
    assert 0 < metadata['size_in_bytes'] <= decomposition.MAX_ZIP
    logical = 0
    with open_archive(partial) as archive:
        assert 'receipt.json' not in archive.namelist()
        archived_fresh(archive, partial['modules'])
        for name, row in partial['modules'].items():
            assert decomposition.identity(name, row) == decomposition.identity(name, original[name])
            for relative, digest, size in output_members(name, row):
                actual = archive.getinfo(relative).file_size
                assert size is None or actual == size
                logical += actual
                assert logical <= 2 * 1024**3
                with archive.open(relative) as stream:
                    assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
    return logical


def check_frontiers(frontiers, spec):
    assert frontiers['status'] == 'COMPLETE_ORIGINAL_NUMERIC166_ZERO_FRESH_FRONTIER_BOUND_NO_NEW_KERNEL_PROOF'
    assert frontiers['endpoints'] == decomposition.ENDPOINTS
    assert frontiers['required_modules'] == 160 and frontiers['fresh_modules'] == []
    rows = frontiers['frontiers']
    assert len(rows) == 10
    for endpoint, row in zip(decomposition.ENDPOINTS, rows):
        assert row['endpoint'] == endpoint and row['within_bound'] is True
        assert row['fresh_modules'] == []
        count = 94 if endpoint in decomposition.ENDPOINTS[6:] else 75
        assert row['required_modules'] == row['verified_prior_objects'] == count


def authenticate_completion(item, artifact, context, fresh, hashes, closures, api):
    from rg_collect_exact_d1_reproductions import records_from_log
    assert fresh == {}, 'The complete batch join must not introduce fresh objects'
    spec, original, base, partial, snapshots = (context[k] for k in
        ('spec', 'original', 'base', 'partial', 'snapshots'))
    for name in spec['required_modules']:
        assert hashes[name] == spec['required_source_sha256'][name]
        assert closures[name] == spec['required_source_closure_sha256'][name]
    run = api.get('/actions/runs/' + str(item['run']))
    assert run['id'] == item['run'] and run['head_sha'] == item['source_commit']
    assert run['path'] == decomposition.WORKFLOW and run['head_branch'] == 'rg-degree-one-large-20261103'
    assert run['repository']['full_name'] == decomposition.REPOSITORY
    join_job = checked_job(api, item, JOB_NAME, SUCCESS_STEP, item['actual_run_attempt'])
    assert item['artifact_name'] == f"rg-d1-numeric166-complete-{item['run']}-{join_job['run_attempt']}"
    checked_artifact(artifact, item, 32 * 1024**2)
    join_origin = {k: item[k] for k in DESCRIPTOR_KEYS - {'repository'}}
    join_origin['repository'] = decomposition.REPOSITORY
    raw = fetch_archive(join_origin)
    assert len(raw) == artifact['size_in_bytes']
    with small_archive(raw, item['artifact_sha256']) as archive:
        assert not any(n.endswith(('.olean', '.ilean', '.server', '.private', '.zip')) for n in archive.namelist())
        assert not any(n.startswith('Proofs.') and n.endswith('.json') for n in archive.namelist())
        manifests_raw = archive.read('numeric166_leaf_manifests.json')
        manifests = json.loads(manifests_raw)
        assert set(manifests) == set(decomposition.KEYS)
        named_raw = archive.read('named_profile_audits.json')
        saved_named = json.loads(named_raw)
        saved_audits = json.loads(archive.read('numeric166_leaf_audits.json'))
        audits, preserved = {}, dict(partial['modules'])
        logical = authenticate_partial(api, partial, original)
        for key in decomposition.KEYS:
            manifest = manifests[key]
            origin = item['compiled_leaf_origins'][key]
            assert decomposition.origin_descriptor(manifest) == origin
            assert (manifest['mathlib'], manifest['leancert'], manifest['lean_version']) == (
                decomposition.PIN, decomposition.LC, '4.33.1')
            leaf = spec['leaf_jobs'][key]
            job = checked_job(api, origin, leaf['job_name'], leaf['required_success_step'])
            assert origin['artifact_name'] == leaf['artifact_name_template'].format(
                run=origin['run'], attempt=job['run_attempt'])
            meta = api.get('/actions/artifacts/' + str(origin['artifact_id']))
            checked_artifact(meta, origin, decomposition.MAX_ZIP)
            leaf_raw = fetch_archive(manifest)
            assert len(leaf_raw) == meta['size_in_bytes'] and sha(leaf_raw) == origin['artifact_sha256']
            with tempfile.TemporaryDirectory(prefix='rg-final-numeric166-') as directory:
                path = pathlib.Path(directory) / 'leaf.zip'
                path.write_bytes(leaf_raw)
                del leaf_raw
                rows, audit = decomposition.authenticate_leaf(path, key, spec, original, base, snapshots[key])
                assert rows == manifest['modules'] == records_from_log(api.logs(origin['job']))
                with zipfile.ZipFile(path) as leaf_archive:
                    saved = json.loads(leaf_archive.read('numeric166_leaf_verified.json'))
                    assert saved['source_commit'] == origin['source_commit']
                    assert saved['workflow_run'] == origin['run'] and saved['workflow_attempt'] == job['run_attempt']
            assert manifest['origin_context'] == dict(
                kind='AUTHENTICATED_DECLARATION_PRESERVING_ORIGINAL_NUMERIC166_LEAF',
                key=key, spec_sha256=SPEC_SHA, run_attempt=job['run_attempt'],
                receipt_sha256=audit['receipt_sha256'], required_modules=94, fresh_modules=20,
                original_definitions=133, original_theorems=313,
                named_profile_sha256=sha(json.dumps(audit['named_axiom_audit'], separators=(',', ':')).encode()))
            assert not preserved.keys() & rows.keys()
            preserved.update(rows)
            audits[key] = audit
            logical += audit['verified_fresh_output_bytes']
            assert logical <= 8 * 1024**3
        assert set(preserved) == decomposition.NEW | set(decomposition.ENDPOINTS[:6])
        assert saved_audits == audits
        assert saved_named == {k: audit['named_axiom_audit'] for k, audit in audits.items()}
        receipt_raw = archive.read('receipt.json')
        checked = decomposition.check_zero_receipt(spec, original, base, partial, manifests, receipt_raw)
        diagnostics = json.loads(archive.read('diagnostics_records.json'))['modules']
        records = {r['module']: r for r in diagnostics}
        assert len(records) == len(diagnostics)
        receipt_records = json.loads(receipt_raw)['modules']
        assert set(receipt_records) <= set(records)
        assert all(records[name] == row for name, row in receipt_records.items())
        # The unchanged base capsule can restore unused sibling modules. They
        # are diagnostics, never additional members of the exact 160 receipt.
        for name in set(records) - set(receipt_records):
            assert name in base['modules']
            assert records[name]['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            assert records[name]['origin'] == decomposition.base_origin(base, name)
            assert decomposition.identity(name, records[name]) == decomposition.identity(name, base['modules'][name])
        decomposition.check_resource(json.loads(archive.read('resource_observer.json')), 0)
        check_frontiers(json.loads(archive.read('numeric166_join_frontier.json')), spec)
        report = json.loads(archive.read('numeric166_complete_verified.json'))
        for key, value in checked.items():
            if key != 'status':
                assert report[key] == value, ('Changed complete batch report', key)
        assert report['status'] == 'COMPLETE_ORIGINAL_NUMERIC166_BATCH_WITH_DECLARATION_PRESERVING_SPLITS'
        assert report['spec_sha256'] == SPEC_SHA and report['source_commit'] == item['source_commit']
        assert report['workflow_run'] == item['run'] and report['workflow_attempt'] == item['actual_run_attempt']
        assert report['named_profile_audits_sha256'] == sha(named_raw)
        assert report['leaf_manifests_sha256'] == sha(manifests_raw)
        assert report['verified_original_and_current_output_bytes'] == logical
        assert report['compiled_leaf_origins'] == item['compiled_leaf_origins']
    context['authenticated_leaf_manifests'] = manifests
    return preserved, dict(
        kind=KIND, required_modules=160, original_endpoints=10,
        actual_compiled_leaf_modules=80, preserved_old_endpoint_objects=6,
        current_source_exports=sorted(decomposition.NEW), audit_fresh_exports=0,
        compiled_leaf_origins=item['compiled_leaf_origins'],
        successful_join_origin=join_origin, original_partial_origin=decomposition.partial_origin(partial),
        join_receipt_sha256=sha(receipt_raw), completion_spec_sha256=SPEC_SHA,
        old_failed_job_status='UNCHANGED_FAILURE', prior_records_relabelled_as_fresh=False,
        named_original_declarations_verified=1252,
        complete_original_axiom_profile_arrays_preserved=True,
        actual_original_and_current_output_bytes_verified=logical,
        full_degree_one_large_closure='PENDING_SEPARATE_FINAL_ASSEMBLY')
