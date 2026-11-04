"""Bind only four separately authenticated actual numeric completion origins.

The three exact historical wave-two reproductions have a separate provenance
kind. Their original master observations never invent failures. Numeric166
retains its failed original job, four actual kernel leaf origins and successful
zero-fresh batch join. This registry never changes a batch proof scope.
"""
import hashlib
import json
import pathlib
import re

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
MASTER = 41686621300
MASTER_HEAD = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
BRANCH = 'rg-degree-one-large-20261103'
SPEC = 'ci/rg_d1_required_numeric_batches_20261103.json'
SPEC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
REGISTRY = 'ci/rg_actual_numeric_completion_origins_20261104.json'
# All four actual jobs and complete archives were authenticated before this digest was sealed.
REGISTRY_SHA = '9cd264e3327d0497cc34418b8d6b3b9f8dfab3dad7bf207c8d82964eaa302663'
THREE_KIND = 'EXACT_REGISTERED_THREE_WAVE_TWO_BATCH_COMPLETION'
THREE = {'00_129', '10_044', '30_013'}
THREE_RUN = 41747378579
THREE_HEAD = '4fa94febfa1782e3840f2b04440e02dab54eec8d'
THREE_WORKFLOW = '.github/workflows/rg-d1-wave-two-three-original-20261104.yml'
THREE_SCOPE = 'ci/rg_d1_wave_two_three_original_20261104.json'
THREE_SCOPE_SHA = '361351f15d89d7b25279f277bc2875bf98ae03e8318605f792c8c2f6db81a172'
JOIN_KIND = 'NUMERIC166_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_BATCH_JOIN'
COMPILED_RUN = 41745244804
COMPILED_HEAD = 'dbb82a7d98eb27b70dc4462dbed8683842b61f6b'
JOIN_RUN = 41752314904
JOIN_HEAD = '228fa2025b3d02670554946916cc7fd4605eddb4'
JOIN_WORKFLOW = '.github/workflows/rg-d1-numeric166-zero-fresh-join-20261104.yml'
JOIN_SCOPE = 'ci/rg_d1_numeric166_decomposed_20261104_spec.json'
JOIN_SCOPE_SHA = '0ddb0d67758c7627ddc7fae947a7100bcb94c9ea6b26ab3f9c13fef33f7d8f8c'
JOIN_AUDIT_SPEC = 'ci/rg_d1_numeric166_zero_fresh_join_20261104_spec.json'
JOIN_AUDIT_SPEC_SHA = '631b58238e9196ec58f80380cbec84d3a8507b8b1a21a92d0cb31569d899179c'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound(root, relative, digest, size=None):
    path = pathlib.PurePosixPath(relative)
    assert not path.is_absolute() and path.parts[0] == 'ci' and '..' not in path.parts
    full = root / path
    assert full.resolve().is_relative_to(root.resolve())
    raw = full.read_bytes()
    assert re.fullmatch(r'[0-9a-f]{64}', digest) and sha(raw) == digest
    assert size is None or type(size) is int and size == len(raw)
    return json.loads(raw)


def context(root):
    assert isinstance(REGISTRY_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', REGISTRY_SHA)
    assert type(JOIN_RUN) is int and JOIN_RUN > 0 and JOIN_RUN != COMPILED_RUN
    assert isinstance(JOIN_HEAD,str) and re.fullmatch(r'[0-9a-f]{40}',JOIN_HEAD)
    assert JOIN_HEAD != COMPILED_HEAD
    registry = bound(root, REGISTRY, REGISTRY_SHA)
    assert set(registry) == {'kind', 'repository', 'numeric_run', 'numeric_source_commit',
        'numeric_spec_sha256', 'jobs'}
    assert registry['kind'] == 'REGISTERED_ACTUAL_AUTHENTICATED_NUMERIC_COMPLETION_ORIGINS'
    assert registry['repository'] == REPOSITORY
    assert registry['numeric_run'] == MASTER and registry['numeric_source_commit'] == MASTER_HEAD
    assert registry['numeric_spec_sha256'] == SPEC_SHA
    assert set(registry['jobs']) == THREE | {'00_166'}
    spec = bound(root, SPEC, SPEC_SHA)
    plans = {p['batch']: p for p in spec['jobs']}
    assert len(plans) == len(spec['jobs']) == 349
    three = bound(root, THREE_SCOPE, THREE_SCOPE_SHA)
    assert three['kind'] == 'EXACT_ORIGINAL_THREE_WAVE_TWO_BATCH_REPRODUCTION'
    assert set(three['batch_ids']) == THREE and len(three['batch_ids']) == 3
    assert {p['batch']:p for p in three['jobs']} == {b:plans[b] for b in THREE}
    assert (three['workers'], three['module_timeout'], three['memory_reserve_mib'],
        three['maximum_parallel_jobs'], three['fresh_module_count']) == (2,1200,2048,2,34)
    joined = bound(root, JOIN_SCOPE, JOIN_SCOPE_SHA)
    assert joined['batch_id'] == '00_166' and joined['original_plan_sha256'] == plans['00_166']['plan_sha256']
    assert (joined['required_module_count'], joined['fresh_module_count'],
        joined['workers'], joined['module_timeout'], joined['memory_reserve_mib']) == (160,80,1,1200,2048)
    join_audit = bound(root,JOIN_AUDIT_SPEC,JOIN_AUDIT_SPEC_SHA)
    assert join_audit['kind'] == 'EXACT_ACTUAL_NUMERIC166_LEAF_ORIGINS_FOR_SEPARATE_ZERO_FRESH_JOIN'
    assert join_audit['compiled_run'] == COMPILED_RUN and join_audit['compiled_source_commit'] == COMPILED_HEAD
    assert (join_audit['required_modules'],join_audit['join_fresh_modules'],
        join_audit['generic_preflight_cli_bound'],join_audit['required_actual_frontier']) == (160,0,1,[])
    for batch, entry in registry['jobs'].items():
        assert set(entry) == {'item', 'authentication_report'}
        item = entry['item']
        common = {'batch', 'original_plan_sha256', 'run', 'job', 'source_commit',
            'artifact_id', 'artifact_sha256', 'artifact_name', 'job_name',
            'workflow_path', 'required_success_step'}
        assert item['batch'] == batch and item['original_plan_sha256'] == plans[batch]['plan_sha256']
        assert all(type(item[k]) is int and item[k] > 0 for k in ('run','job','artifact_id'))
        assert re.fullmatch(r'[0-9a-f]{40}', item['source_commit'])
        assert re.fullmatch(r'[0-9a-f]{64}', item['artifact_sha256'])
        if batch in THREE:
            assert set(item) == common | {'provenance_kind'}
            assert item['provenance_kind'] == THREE_KIND and plans[batch]['wave'] == 2
            assert item['run'] == THREE_RUN and item['source_commit'] == THREE_HEAD
            assert item['workflow_path'] == THREE_WORKFLOW
            assert item['job_name'] == 'reproduce-original-wave-two-' + batch
            assert item['artifact_name'] == f'rg-d1-wave-two-three-original-20261104-{THREE_RUN}-1-{batch}'
            assert item['required_success_step'] == 'Require exact historical output identities'
        else:
            assert set(item) == common | {'original_job', 'completion_kind',
                'completion_spec', 'compiled_leaf_origins', 'completion_join_spec'}
            assert item['original_job'] == 126095241107
            assert item['completion_kind'] == JOIN_KIND
            assert item['run'] == JOIN_RUN and item['source_commit'] == JOIN_HEAD
            assert item['workflow_path'] == JOIN_WORKFLOW
            assert item['job_name'] == 'Join complete original numeric166 batch'
            assert item['artifact_name'] == f'rg-d1-numeric166-complete-{JOIN_RUN}-1'
            assert item['required_success_step'] == 'Require full original batch and all preserved origins'
            assert item['completion_spec'] == {'path':JOIN_SCOPE,'sha256':JOIN_SCOPE_SHA}
            assert item['completion_join_spec'] == {'path':JOIN_AUDIT_SPEC,'sha256':JOIN_AUDIT_SPEC_SHA}
            leaves = item['compiled_leaf_origins']
            assert set(leaves) == {'01666','01667','01668','01669'}
            assert leaves == join_audit['compiled_leaf_origins']
            for key, leaf in leaves.items():
                assert set(leaf) == {'repository','run','job','source_commit','artifact_id',
                    'artifact_sha256','artifact_name'}
                assert leaf['repository'] == REPOSITORY
                assert leaf['run'] == COMPILED_RUN and leaf['source_commit'] == COMPILED_HEAD
                assert leaf['artifact_name'] == f'rg-d1-numeric166-leaf-{key}-{COMPILED_RUN}-1'
                assert all(type(leaf[k]) is int and leaf[k] > 0 for k in ('run','job','artifact_id'))
                assert re.fullmatch(r'[0-9a-f]{64}', leaf['artifact_sha256'])
            assert len({p['job'] for p in leaves.values()} | {item['job']}) == 5
            assert len({p['artifact_id'] for p in leaves.values()} | {item['artifact_id']}) == 5
        report_ref = entry['authentication_report']
        assert set(report_ref) == {'path','sha256','bytes'}
        report = bound(root, report_ref['path'], report_ref['sha256'], report_ref['bytes'])
        for key in ('run','job','source_commit','artifact_id','artifact_sha256','original_plan_sha256'):
            assert report[key] == item[key], ('Changed authenticated origin report',batch,key)
        if batch in THREE:
            assert report['status'] == 'ACTUAL_THREE_BATCH_MEMBER_ARCHIVE_AND_ORIGINAL_IDENTITIES_AUTHENTICATED'
            assert (report['required_modules'], report['fresh_modules']) == {
                '00_129':(76,2), '10_044':(87,16), '30_013':(77,16)}[batch]
            assert report['original_source_closure_object_axiom_member_identities_matched'] == report['fresh_modules']
            assert (report['actual_workers'], report['module_timeout'], report['memory_reserve_mib']) == (2,1200,2048)
            assert report['original_master_job_status_relabelled'] is False
            assert report['degree_one_large_completion_claimed'] is False
        else:
            assert report['status'] == 'ACTUAL_NUMERIC166_FULL_ZERO_FRESH_JOIN_AND_ALL_COMPILED_ORIGINS_AUTHENTICATED'
            assert report['compiled_leaf_origins'] == item['compiled_leaf_origins']
            assert report['join_spec_sha256'] == JOIN_AUDIT_SPEC_SHA
            assert (report['current_source_modules'], report['original_endpoints'], report['fresh_join_modules'],
                report['actual_compiled_leaf_modules'], report['unchanged_old_endpoints']) == (160,10,0,80,6)
            assert (report['original_definitions_preserved'], report['original_theorems_preserved'],
                report['original_named_axiom_profiles_preserved']) == (532,1252,1252)
            assert report['old_failed_job_status'] == 'UNCHANGED_FAILURE'
            assert report['prior_records_relabelled_as_fresh'] is False
            assert report['resource_guards_unchanged'] is True and report['standard_axioms_only'] is True
            assert report['whole_numeric166_batch_claimed'] is True
            assert report['whole_degree_one_large_claimed'] is False
    return registry


def original_observation(batch, old):
    assert batch in THREE
    if old is not None:
        assert old['run_id'] == MASTER and old['head_sha'] == MASTER_HEAD
        assert type(old['run_attempt']) is int and old['run_attempt'] == 1
        assert old['head_branch'] == BRANCH and old['name'] == 'original-numeric-' + batch
    return dict(run=MASTER, source_commit=MASTER_HEAD, run_attempt=1,
        job_name='original-numeric-'+batch, job=old['id'] if old else None,
        status=old['status'] if old else 'not_created', conclusion=old['conclusion'] if old else None)


def three_binding(item, spec_raw, origin, root):
    assert item['provenance_kind'] == THREE_KIND
    assert not {'original_job','original_job_lookup','completion_kind'} & item.keys()
    assert origin['repository'] == REPOSITORY and origin['run'] == MASTER
    assert origin['source_commit'] == MASTER_HEAD and sha(spec_raw) == SPEC_SHA
    assert item['batch'] in THREE
    expected = context(root)['jobs'][item['batch']]['item']
    assert set(item) == set(expected) | {'original_job_observation'}
    assert {k:item[k] for k in expected} == expected
    observation = item['original_job_observation']
    assert set(observation) == {'run','source_commit','run_attempt','job_name','job','status','conclusion'}
    assert type(observation['run']) is int and observation['run'] == MASTER
    assert observation['source_commit'] == MASTER_HEAD
    assert type(observation['run_attempt']) is int and observation['run_attempt'] == 1
    assert observation['job_name'] == 'original-numeric-' + item['batch']
    if observation['status'] == 'not_created':
        assert observation['job'] is None and observation['conclusion'] is None
    else:
        assert type(observation['job']) is int and observation['job'] > 0
        assert observation['status'] in ('queued','waiting','in_progress','completed')
        if observation['status'] == 'completed':
            assert observation['conclusion'] in ('success','failure','timed_out','cancelled',
                'skipped','neutral','action_required','stale','startup_failure')
        else:
            assert observation['conclusion'] is None
    return observation


def observe_three_original_job(item, spec_raw, origin, jobs, root):
    captured = three_binding(item, spec_raw, origin, root)
    matches = [j for j in jobs if j['name'] == captured['job_name']]
    assert len(matches) <= 1, ('Ambiguous original three-batch job', item['batch'])
    if not matches:
        assert captured['status'] == 'not_created', 'Previously observed original job disappeared'
        return dict(captured)
    job = matches[0]
    assert type(job['id']) is int and job['id'] > 0
    observed = original_observation(item['batch'],job)
    if captured['job'] is not None:
        assert observed['job'] == captured['job'], 'Original job identity changed'
    three_binding(dict(item,original_job_observation=observed),spec_raw,origin,root)
    return observed
