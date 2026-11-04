"""Join the four actual numeric166 proof origins without compiling them again.

The generic restore helper requires a positive CLI cap. Its preflight-only
mode is called with cap one, then this controller requires an exactly empty
frontier for every endpoint before the strict verifier can run. The resulting
160-module receipt must contain only prior exports with their original origins.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

import rg_numeric166_decomposed_recovery as d

ROOT = d.ROOT
SPEC = 'ci/rg_d1_numeric166_zero_fresh_join_20261104_spec.json'
SPEC_SHA = '631b58238e9196ec58f80380cbec84d3a8507b8b1a21a92d0cb31569d899179c'
WORKFLOW = '.github/workflows/rg-d1-numeric166-zero-fresh-join-20261104.yml'
DESCRIPTOR_KEYS = {'repository', 'run', 'job', 'source_commit', 'artifact_id',
                   'artifact_sha256', 'artifact_name'}


def load_join_spec(join_spec_sha):
    """Read and validate the immutable actual-origin binding; no writes or API."""
    raw = (ROOT / SPEC).read_bytes()
    assert join_spec_sha == SPEC_SHA and d.sha(raw) == join_spec_sha
    spec = json.loads(raw)
    assert set(spec) == {'kind', 'decomposition_spec', 'decomposition_controller',
        'compiled_run', 'compiled_source_commit', 'compiled_leaf_origins', 'failed_join',
        'required_modules', 'original_endpoints', 'actual_compiled_leaf_modules',
        'preserved_original_endpoint_objects', 'join_fresh_modules',
        'generic_preflight_cli_bound', 'required_actual_frontier',
        'module_timeout_seconds', 'memory_reserve_mib'}
    assert spec['kind'] == 'EXACT_ACTUAL_NUMERIC166_LEAF_ORIGINS_FOR_SEPARATE_ZERO_FRESH_JOIN'
    assert spec['decomposition_spec'] == {'path': d.SPEC,
        'sha256': '0ddb0d67758c7627ddc7fae947a7100bcb94c9ea6b26ab3f9c13fef33f7d8f8c'}
    assert spec['decomposition_controller'] == {'path': 'ci/rg_numeric166_decomposed_recovery.py',
        'sha256': '45b783d210badce44772f13cd3bec5f7b424dd6b5548660b140b9e559d6e3071'}
    for descriptor in (spec['decomposition_spec'], spec['decomposition_controller']):
        assert d.digest_file(ROOT / descriptor['path']) == descriptor['sha256']
    assert spec['compiled_run'] == 41745244804
    assert spec['compiled_source_commit'] == 'dbb82a7d98eb27b70dc4462dbed8683842b61f6b'
    for key, value in {'required_modules': 160, 'original_endpoints': 10,
        'actual_compiled_leaf_modules': 80, 'preserved_original_endpoint_objects': 6,
        'join_fresh_modules': 0, 'generic_preflight_cli_bound': 1,
        'required_actual_frontier': [], 'module_timeout_seconds': 1200,
        'memory_reserve_mib': 2048}.items():
        assert spec[key] == value
    assert set(spec['compiled_leaf_origins']) == set(d.KEYS)
    jobs, artifacts = set(), set()
    for key, origin in spec['compiled_leaf_origins'].items():
        assert set(origin) == DESCRIPTOR_KEYS and origin['repository'] == d.REPOSITORY
        assert origin['run'] == spec['compiled_run']
        assert origin['source_commit'] == spec['compiled_source_commit']
        assert origin['artifact_name'] == f"rg-d1-numeric166-leaf-{key}-{origin['run']}-1"
        assert re.fullmatch(r'[0-9a-f]{64}', origin['artifact_sha256'])
        for field, used in (('job', jobs), ('artifact_id', artifacts)):
            assert type(origin[field]) is int and origin[field] > 0 and origin[field] not in used
            used.add(origin[field])
    failed = spec['failed_join']
    assert failed['run'] == spec['compiled_run'] and failed['source_commit'] == spec['compiled_source_commit']
    assert failed['job'] == 126315670675 and failed['artifact_id'] == 13285803871
    assert failed['artifact_sha256'] == 'ef9868e8706bb7edb9ec83ac3686684a8167a4f05c3d47002fdcb7c93e51230c'
    assert failed['failure'] == 'PREFLIGHT_CLI_REQUIRES_POSITIVE_CAP_ZERO_FRONTIER_NOT_YET_CHECKED'
    return spec


def actual_join_identity(binding, api):
    assert os.environ['GITHUB_REPOSITORY'] == d.REPOSITORY
    run = int(os.environ['GITHUB_RUN_ID'])
    commit = os.environ['GITHUB_SHA']
    attempt = int(os.environ['GITHUB_RUN_ATTEMPT'])
    assert run > 0 and run != binding['compiled_run'] and attempt > 0
    assert re.fullmatch(r'[0-9a-f]{40}', commit) and commit != binding['compiled_source_commit']
    metadata = api.get('/actions/runs/' + str(run))
    assert metadata['id'] == run and metadata['head_sha'] == commit and metadata['path'] == WORKFLOW
    assert metadata['repository']['full_name'] == d.REPOSITORY
    assert metadata['head_branch'] == 'rg-degree-one-large-20261103'
    assert metadata['run_attempt'] == attempt
    return run, commit, attempt


def collect_actual_leaves(binding, spec, expected, base, snapshots):
    from rg_github_artifacts import fetch_archive
    api = d.GitHub()
    actual_join_identity(binding, api)
    run = binding['compiled_run']
    metadata = api.get('/actions/runs/' + str(run))
    assert metadata['id'] == run and metadata['head_sha'] == binding['compiled_source_commit']
    assert metadata['path'] == d.WORKFLOW and metadata['repository']['full_name'] == d.REPOSITORY
    assert metadata['head_branch'] == 'rg-degree-one-large-20261103'
    jobs = api.listing('/actions/runs/' + str(run) + '/jobs?filter=all', 'jobs')
    artifacts = api.listing('/actions/runs/' + str(run) + '/artifacts', 'artifacts')
    manifests, audits, covered = {}, {}, set()
    directory = ROOT / 'ci/rg_numeric166_decomposed_exports' / str(run)
    directory.mkdir(parents=True, exist_ok=True)
    for key in d.KEYS:
        origin = binding['compiled_leaf_origins'][key]
        selected = [job for job in jobs if job['id'] == origin['job']]
        assert len(selected) == 1
        job = selected[0]
        leaf = spec['leaf_jobs'][key]
        assert job['run_id'] == run and job['head_sha'] == origin['source_commit']
        assert job['name'] == leaf['job_name'] and job['run_attempt'] == 1
        assert job['head_branch'] == 'rg-degree-one-large-20261103'
        assert job['status'] == 'completed' and job['conclusion'] == 'success'
        steps = [s for s in job['steps'] if s['name'] == leaf['required_success_step']]
        assert len(steps) == 1 and steps[0]['status'] == 'completed' and steps[0]['conclusion'] == 'success'
        selected = [a for a in artifacts if a['id'] == origin['artifact_id']]
        assert len(selected) == 1
        artifact = selected[0]
        assert artifact['name'] == origin['artifact_name'] and not artifact['expired']
        assert artifact['digest'] == 'sha256:' + origin['artifact_sha256']
        assert artifact['workflow_run']['id'] == run and artifact['workflow_run']['head_sha'] == origin['source_commit']
        assert artifact['workflow_run']['head_branch'] == 'rg-degree-one-large-20261103'
        assert 0 < artifact['size_in_bytes'] <= d.MAX_ZIP
        manifest = dict(origin, lean_version='4.33.1', mathlib=d.PIN, leancert=d.LC)
        raw = fetch_archive(manifest)
        assert len(raw) == artifact['size_in_bytes'] and d.sha(raw) == origin['artifact_sha256']
        with tempfile.TemporaryDirectory(prefix='rg-numeric166-fixed-origin-') as temporary:
            path = pathlib.Path(temporary) / 'leaf.zip'
            path.write_bytes(raw)
            del raw
            fresh, audit = d.authenticate_leaf(path, key, spec, expected, base, snapshots[key])
            assert not covered & set(fresh)
            covered.update(fresh)
            manifest['modules'] = dict(sorted(fresh.items()))
            manifest['origin_context'] = dict(kind='AUTHENTICATED_DECLARATION_PRESERVING_ORIGINAL_NUMERIC166_LEAF',
                key=key, spec_sha256=binding['decomposition_spec']['sha256'], run_attempt=1,
                receipt_sha256=audit['receipt_sha256'], required_modules=94, fresh_modules=20,
                original_definitions=133, original_theorems=313,
                named_profile_sha256=d.sha(json.dumps(audit['named_axiom_audit'], separators=(',', ':')).encode()))
            target = directory / ('leaf' + key + '.json')
            d.save(target, manifest)
            subprocess.run([sys.executable, '-B', 'ci/rg_restore_job_exports.py',
                '--manifest', str(target), '--build-directory', str(d.BUILD),
                '--verified-local-archive', str(path)], cwd=ROOT, check=True)
        manifests[key] = manifest
        audits[key] = audit
        print(json.dumps(dict(status='AUTHENTICATED_UNCHANGED_NUMERIC166_COMPILED_ORIGIN',
            key=key, **origin, fresh_modules=20)), flush=True)
    assert covered == d.NEW and len(covered) == 80
    assert {key: d.origin_descriptor(m) for key, m in manifests.items()} == binding['compiled_leaf_origins']
    d.save(d.EXPORTS / 'numeric166_leaf_manifests.json', manifests)
    d.save(d.EXPORTS / 'named_profile_audits.json', {key: a['named_axiom_audit'] for key, a in audits.items()})
    d.save(d.EXPORTS / 'numeric166_leaf_audits.json', audits)


def require_zero_frontier(report):
    assert report['status'] == 'COMPLETE_ORIGINAL_NUMERIC166_ZERO_FRESH_FRONTIER_BOUND_NO_NEW_KERNEL_PROOF'
    assert report['endpoints'] == d.ENDPOINTS and report['required_modules'] == 160
    assert report['fresh_modules'] == [] and len(report['frontiers']) == 10
    for endpoint, row in zip(d.ENDPOINTS, report['frontiers']):
        assert row['endpoint'] == endpoint and row['within_bound'] is True
        assert row['max_fresh'] == 1 and row['fresh_modules'] == []
        count = 94 if endpoint in d.ENDPOINTS[6:] else 75
        assert row['required_modules'] == row['verified_prior_objects'] == count


def zero_preflight():
    frontiers = []
    for endpoint in d.ENDPOINTS:
        subprocess.run([sys.executable, '-B', 'ci/rg_restore_with_kernel_fallback.py',
            '--plan', 'ci/rg_empty_restore_plan.json', '--build-directory', str(d.BUILD),
            '--endpoint', endpoint, '--max-fresh', '1', '--workers', '1', '--preflight-only'],
            cwd=ROOT, check=True)
        frontier = json.loads((d.BUILD / 'bounded_kernel_fallback_plan.json').read_bytes())
        assert frontier['endpoint'] == endpoint and frontier['within_bound'] is True
        assert frontier['fresh_modules'] == [], 'Numeric166 join must restore every object before verification'
        frontiers.append(frontier)
    report = dict(status='COMPLETE_ORIGINAL_NUMERIC166_ZERO_FRESH_FRONTIER_BOUND_NO_NEW_KERNEL_PROOF',
        endpoints=d.ENDPOINTS, required_modules=160, fresh_modules=[], frontiers=frontiers)
    require_zero_frontier(report)
    d.save(d.EXPORTS / 'numeric166_join_frontier.json', report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--join-spec-sha256', required=True)
    parser.add_argument('--phase', choices=('collect', 'preflight', 'kernel', 'compare'), required=True)
    args = parser.parse_args()
    binding = load_join_spec(args.join_spec_sha256)
    spec, plan, expected, base, partial, snapshots = d.context(binding['decomposition_spec']['sha256'])
    d.preserve_declarations(spec, expected, snapshots)
    d.source_scope(spec, expected, base, partial)
    d.EXPORTS.mkdir(parents=True, exist_ok=True)
    if args.phase == 'collect':
        collect_actual_leaves(binding, spec, expected, base, snapshots)
    elif args.phase == 'preflight':
        zero_preflight()
    elif args.phase == 'kernel':
        require_zero_frontier(json.loads((d.EXPORTS / 'numeric166_join_frontier.json').read_bytes()))
        d.kernel(d.ENDPOINTS)
    else:
        manifests = json.loads((d.EXPORTS / 'numeric166_leaf_manifests.json').read_bytes())
        assert {key: d.origin_descriptor(m) for key, m in manifests.items()} == binding['compiled_leaf_origins']
        require_zero_frontier(json.loads((d.EXPORTS / 'numeric166_join_frontier.json').read_bytes()))
        report = d.validate_complete_receipt(spec, expected, base, partial,
            (d.BUILD / 'receipt.json').read_bytes(), manifests,
            lambda p: d.local(p).read_bytes(), lambda p: d.local(p).open('rb'), lambda p: d.local(p).stat().st_size)
        d.check_resource(json.loads((d.EXPORTS / 'resource_observer.json').read_bytes()), 0)
        report.update(spec_sha256=binding['decomposition_spec']['sha256'],
            join_spec_sha256=args.join_spec_sha256, source_commit=os.environ['GITHUB_SHA'],
            workflow_run=int(os.environ['GITHUB_RUN_ID']), workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
            named_profile_audits_sha256=d.digest_file(d.EXPORTS / 'named_profile_audits.json'),
            leaf_manifests_sha256=d.digest_file(d.EXPORTS / 'numeric166_leaf_manifests.json'),
            failed_original_join_status='UNCHANGED_FAILURE', compiled_objects_reexported_as_fresh=False)
        d.save(d.EXPORTS / 'numeric166_complete_verified.json', report)
        print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
