"""Authenticate original compact-family exports from exact preceding jobs.

Only complete archives from successful same-commit jobs may become restoration
manifests. Every fresh source, closure, object, axiom profile and output member
must reproduce its sealed historical identity before optional local restore.
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
import urllib.request
import zipfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'Proofs/RG_Lean_20261019'))
from module_outputs import check_archive_outputs, output_members
from rg_github_artifacts import fetch_archive
from rg_github_rate_limit import api_open

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MAX_ZIP = 1024 ** 3
MAX_OUTPUT = 2 * 1024 ** 3
WORKFLOW = '.github/workflows/rg-compact-closed-support-reconstruction-20261103.yml'


def identity(name, row):
    assert row['module'] == name
    assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
    return (row['source_sha256'], row['source_closure_sha256'], row['output_sha256'],
            row['axiom_profiles'], tuple(sorted(output_members(name, row))))


class GitHub:
    def __init__(self, repository):
        assert re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository)
        self.base = 'https://api.github.com/repos/' + repository
        self.headers = {'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'],
                        'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'}

    def get(self, suffix):
        with api_open(urllib.request.Request(self.base + suffix, headers=self.headers)) as response:
            return json.load(response)

    def listing(self, suffix, member):
        rows = []
        for page in range(1, 101):
            separator = '&' if '?' in suffix else '?'
            response = self.get(suffix + separator + 'per_page=100&page=' + str(page))
            current = response[member]
            rows.extend(current)
            assert len({r['id'] for r in rows}) == len(rows)
            if len(rows) == response['total_count']:
                return rows
            assert len(current) == 100 and len(rows) < response['total_count']
        raise AssertionError('Bounded GitHub pagination limit exceeded')


def latest_job(jobs, name, run, commit):
    matches = [j for j in jobs if j['name'] == name]
    assert matches, ('Missing exact prerequisite job', name)
    assert all(j['run_id'] == run and j['head_sha'] == commit for j in matches)
    attempt = max(j['run_attempt'] for j in matches)
    matches = [j for j in matches if j['run_attempt'] == attempt]
    assert len(matches) == 1, ('Ambiguous prerequisite job attempt', name, attempt)
    job = matches[0]
    assert job['status'] == 'completed' and job['conclusion'] == 'success', (name, job['conclusion'])
    steps = [s for s in job['steps'] if s['name'] == 'Require exact historical original identities']
    assert len(steps) == 1 and steps[0]['conclusion'] == 'success', name
    return job


def authenticate(path, expected, endpoints, spec):
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        assert len(names) == len(set(names)), 'Duplicate archive members'
        assert all(not n.startswith('/') and '..' not in pathlib.PurePosixPath(n).parts for n in names)
        receipt_bytes = archive.read('receipt.json')
        receipt = json.loads(receipt_bytes)
        assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE'
        assert receipt['endpoints'] == endpoints
        assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
        assert 'version ' + spec['lean_version'] + ',' in receipt['lean']
        fresh = {n: row for n, row in receipt['modules'].items() if row['mode'] == 'FRESH_KERNEL_EXPORT'}
        assert set(fresh) == set(expected), 'Unexpected fresh module set'
        declared_bytes = sum(archive.getinfo(rel).file_size for n, row in fresh.items()
                             for rel, _, _ in output_members(n, row))
        assert declared_bytes <= MAX_OUTPUT, 'Fresh outputs exceed the explicit two GiB bound'
        checked_bytes = 0
        for name, row in fresh.items():
            assert expected[name]['mode'] == 'FRESH_KERNEL_EXPORT'
            assert identity(name, row) == identity(name, expected[name]), ('Changed historical identity', name)
            assert json.loads(archive.read(name + '.json')) == row
            checked_bytes += check_archive_outputs(archive, name, row)
        assert checked_bytes == declared_bytes
        observer = json.loads(archive.read('resource_observer.json'))
        assert observer['status'] == 'VERIFIER_COMPLETED' and observer['exit_code'] == 0
        assert observer['mathlib_and_lean_flags_unchanged'] is True
    return fresh, {'receipt_sha256': hashlib.sha256(receipt_bytes).hexdigest(),
                   'verified_fresh_output_bytes': checked_bytes, 'fresh_modules': len(fresh)}


def check_existing(build, fresh):
    for name, row in fresh.items():
        record = build / (name + '.json')
        if not record.exists():
            continue
        previous = json.loads(record.read_bytes())
        assert identity(name, previous) == identity(name, row), ('Conflicting restored export', name)
        for rel, digest, size in output_members(name, previous):
            path = build / rel
            assert path.is_file() and (size is None or path.stat().st_size == size)
            with path.open('rb') as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest, ('Changed restored object', name, rel)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--through', choices=('roots', 'support'), required=True)
    p.add_argument('--restore', action='store_true')
    p.add_argument('--build-directory', type=pathlib.Path,
                   default=ROOT / 'Proofs/RG_Lean_20261019/build/extension')
    a = p.parse_args()
    spec = json.loads((ROOT / 'ci/rg_compact_closed_support_20261103.json').read_bytes())
    assert spec['kind'] == 'EXACT_COMPACT_CLOSED_ORIGINAL_SUPPORT_RECONSTRUCTION'
    assert spec['mathlib'] == PIN and spec['leancert'] == LC and spec['lean_version'] == '4.33.1'
    assert len(spec['historical_rows']) == 673 and len(spec['support_modules']) == 143
    assert len(spec['root_batches']) == 17
    roots = [n for batch in spec['root_batches'].values() for n in batch['endpoints']]
    assert len(roots) == len(set(roots)) == 530
    assert not set(roots) & set(spec['support_modules'])
    assert set(roots) | set(spec['support_modules']) == set(spec['historical_rows'])
    repository, run = os.environ['GITHUB_REPOSITORY'], int(os.environ['GITHUB_RUN_ID'])
    commit = os.environ['GITHUB_SHA']
    assert re.fullmatch(r'[0-9a-f]{40}', commit)
    api = GitHub(repository)
    current = api.get('/actions/runs/' + str(run))
    assert current['id'] == run and current['head_sha'] == commit and current['path'] == WORKFLOW
    jobs = api.listing('/actions/runs/' + str(run) + '/jobs?filter=all', 'jobs')
    artifacts = api.listing('/actions/runs/' + str(run) + '/artifacts', 'artifacts')
    items = []
    for key, batch in sorted(spec['root_batches'].items()):
        assert re.fullmatch(r'root[0-9]{2}', key)
        items.append((key, 'compact-roots-' + key, 'rg-compact-roots-' + key,
                      batch['endpoints'], batch['endpoints']))
    if a.through == 'support':
        items.append(('support', 'compact-support-closures', 'rg-compact-support-closures',
                      spec['support_endpoints'], spec['support_modules']))
    build = a.build_directory.resolve()
    output = ROOT / 'ci/rg_reconstructed_compact_support' / str(run)
    output.mkdir(parents=True, exist_ok=True)
    reports, covered = [], set()
    for key, job_name, artifact_prefix, endpoints, module_names in items:
        job = latest_job(jobs, job_name, run, commit)
        artifact_name = f"{artifact_prefix}-{run}-{job['run_attempt']}"
        matches = [m for m in artifacts if m['name'] == artifact_name]
        assert len(matches) == 1, ('Missing or ambiguous original archive', artifact_name)
        artifact = matches[0]
        assert not artifact['expired'] and 0 < artifact['size_in_bytes'] <= MAX_ZIP
        assert artifact['workflow_run']['id'] == run and artifact['workflow_run']['head_sha'] == commit
        assert re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest'])
        manifest = dict(repository=repository, run=run, job=job['id'], source_commit=commit,
                        artifact_id=artifact['id'], artifact_sha256=artifact['digest'].removeprefix('sha256:'),
                        lean_version=spec['lean_version'], mathlib=PIN)
        data = fetch_archive(manifest)
        assert len(data) == artifact['size_in_bytes'] and len(data) <= MAX_ZIP
        assert hashlib.sha256(data).hexdigest() == manifest['artifact_sha256']
        expected = {name: spec['historical_rows'][name] for name in module_names}
        with tempfile.TemporaryDirectory(prefix='rg-compact-original-') as temporary:
            path = pathlib.Path(temporary) / 'original.zip'
            path.write_bytes(data)
            del data
            fresh, audit = authenticate(path, expected, endpoints, spec)
            assert not covered & set(fresh), 'Overlapping declared compact reconstruction frontiers'
            covered.update(fresh)
            manifest['modules'] = dict(sorted(fresh.items()))
            manifest['origin_context'] = dict(kind='AUTHENTICATED_ORIGINAL_COMPACT_RECONSTRUCTION',
                                              run_attempt=job['run_attempt'], **audit)
            destination = output / (key + '.json')
            destination.write_text(json.dumps(manifest, indent=2) + '\n')
            if a.restore:
                check_existing(build, fresh)
                subprocess.run([sys.executable, '-B', str(ROOT / 'ci/rg_restore_job_exports.py'),
                                '--manifest', str(destination), '--build-directory', str(build),
                                '--verified-local-archive', str(path)], check=True)
        report = dict(key=key, job=job['id'], artifact_id=artifact['id'], run_attempt=job['run_attempt'], **audit)
        reports.append(report)
        print(json.dumps(dict(status='AUTHENTICATED_ORIGINAL_COMPACT_EXPORT', **report)), flush=True)
    assert len(covered) == (530 if a.through == 'roots' else 673)
    summary = dict(status='AUTHENTICATED_ORIGINAL_COMPACT_SUPPORT_EXPORTS', through=a.through,
                   run=run, source_commit=commit, fresh_modules=len(covered), archives=len(reports),
                   restored=a.restore, proof_scope='ORIGINAL_PREREQUISITES_ONLY', reports=reports)
    print(json.dumps(summary, separators=(',', ':')), flush=True)


if __name__ == '__main__':
    main()
