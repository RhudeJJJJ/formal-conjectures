"""Authenticate the nine current Fast40 cell jobs and their new kernel exports.

These cells have new acceptance-proof bodies. Their source closures, standard
axioms and actual output bytes are checked without asserting historical object
equality. Only the thirty unchanged prior identities come from the sealed base.
"""
import argparse
import hashlib
import importlib.util
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
SOURCE = ROOT / 'Proofs/RG_Lean_20261019'
sys.path.insert(0, str(SOURCE))
from module_outputs import check_archive_outputs, output_members
from rg_github_artifacts import fetch_archive
from rg_github_rate_limit import api_open

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
WORKFLOW = '.github/workflows/rg-d1-fast40-remaining-staged-recovery-20261103.yml'
SPEC = 'ci/rg_d1_fast40_remaining_staged_20261103_spec.json'
SPEC_SHA256 = '9cc33ff88aec4c5ebe224be3ab8b099c7babc18502bcfef1d0d4914b82be535c'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
KEYS = tuple(f'{i:03d}' for i in range(10, 19))
MAX_ZIP, MAX_OUTPUT, MAX_JSON = 1024 ** 3, 2 * 1024 ** 3, 8 * 1024 ** 2


def digest_file(path):
    with pathlib.Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def profiles(row):
    value = row['axiom_profiles']
    assert isinstance(value, list) and value
    assert all(isinstance(profile, list) and set(profile) <= ALLOWED for profile in value)
    return value


def identity(name, row):
    assert row['module'] == name
    assert re.fullmatch(r'[0-9a-f]{64}', row['output_sha256'])
    return (row['source_sha256'], row['source_closure_sha256'], row['output_sha256'],
            profiles(row), tuple(sorted(output_members(name, row))))


def bound_path(relative, digest):
    relative = pathlib.PurePosixPath(relative)
    assert relative.is_relative_to('ci') and '..' not in relative.parts
    path = ROOT / relative
    assert digest_file(path) == digest, ('Changed sealed input', str(relative))
    return path


def load_spec(path):
    path = pathlib.Path(path).resolve()
    assert path == (ROOT / SPEC).resolve()
    assert digest_file(path) == SPEC_SHA256
    spec = json.loads(path.read_bytes())
    assert spec['kind'] == 'EXACT_FAST40_REMAINING_COMPONENT_RECONSTRUCTION'
    assert spec['lean_version'] == '4.33.1' and spec['mathlib'] == PIN and spec['leancert'] == LC
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib'],
            spec['max_parallel_cell_jobs']) == (1, 600, 2048, 2)
    assert spec['acceptance_proof_bodies_changed'] is True
    assert set(spec['cell_jobs']) == set(KEYS)
    all_fresh = set()
    for key in KEYS:
        cell = spec['cell_jobs'][key]
        assert cell['key'] == key and cell['endpoint'] == 'Proofs.RadenkovicGutmanD1FastFullBox40Cell' + key
        assert cell['required_module_count'] == 37 and cell['fresh_module_count'] == len(cell['modules']) == 7
        assert cell['axiom_profile_counts'] == {name: 1 for name in cell['modules']}
        assert cell['job_name'] == 'cell-' + key
        assert cell['artifact_name_template'] == 'rg-d1-fast40-cell-' + key + '-{run}-{attempt}'
        assert cell['required_success_step'] == 'Require exact staged cell source exports'
        assert not all_fresh & set(cell['modules'])
        all_fresh.update(cell['modules'])
    assert len(all_fresh) == 63 and all_fresh == set(spec['all_new_cell_modules'])
    base = json.loads(bound_path(spec['base_manifest'], spec['base_manifest_sha256']).read_bytes())
    helper_path = bound_path(spec['source_graph_helper'], spec['source_graph_helper_sha256'])
    module_spec = importlib.util.spec_from_file_location('rg_fast40_staged_source_graph', helper_path)
    assert module_spec and module_spec.loader
    graph = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(graph)
    assert graph.PIN == PIN and graph.LC == LC and graph.ALLOWED == ALLOWED
    return spec, base, graph


def source_scope(cell, base, graph):
    hashes, closures = graph.source_graph(cell['endpoint'])
    assert len(hashes) == cell['required_module_count'] == 37
    assert set(hashes) - set(base['modules']) == set(cell['modules'])
    prior = set(hashes) - set(cell['modules'])
    assert len(prior) == 30
    for name in hashes:
        expected = cell['modules'].get(name, base['modules'].get(name))
        assert expected is not None
        assert hashes[name] == expected['source_sha256']
        assert closures[name] == expected['source_closure_sha256']
    return hashes, closures


class GitHub:
    def __init__(self, repository):
        assert repository == REPOSITORY
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
            assert len({row['id'] for row in rows}) == len(rows)
            if len(rows) == response['total_count']:
                return rows
            assert len(current) == 100 and len(rows) < response['total_count']
        raise AssertionError('Bounded GitHub pagination limit exceeded')


def latest_job(jobs, cell, run, commit):
    matches = [job for job in jobs if job['name'] == cell['job_name']]
    assert matches, ('Missing exact cell job', cell['job_name'])
    assert all(job['run_id'] == run and job['head_sha'] == commit for job in matches)
    attempt = max(job['run_attempt'] for job in matches)
    matches = [job for job in matches if job['run_attempt'] == attempt]
    assert len(matches) == 1, ('Ambiguous latest cell attempt', cell['job_name'])
    job = matches[0]
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    steps = [step for step in job['steps'] if step['name'] == cell['required_success_step']]
    assert len(steps) == 1 and steps[0]['conclusion'] == 'success'
    return job


def authenticate(path, cell, spec, base, hashes, closures):
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        assert len(names) == len(set(names)), 'Duplicate archive members'
        assert all(not name.startswith('/') and '..' not in pathlib.PurePosixPath(name).parts for name in names)
        def read_json(name):
            assert archive.getinfo(name).file_size <= MAX_JSON
            return json.loads(archive.read(name))
        receipt_bytes = archive.read('receipt.json') if archive.getinfo('receipt.json').file_size <= MAX_JSON else None
        assert receipt_bytes is not None
        receipt = json.loads(receipt_bytes)
        assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [cell['endpoint']]
        assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
        assert 'version ' + spec['lean_version'] + ',' in receipt['lean']
        assert len(receipt['modules']) == cell['required_module_count'] == 37
        assert set(receipt['modules']) == set(hashes)
        fresh = {name: row for name, row in receipt['modules'].items() if row['mode'] == 'FRESH_KERNEL_EXPORT'}
        assert set(fresh) == set(cell['modules']) and len(fresh) == cell['fresh_module_count'] == 7
        for name, row in receipt['modules'].items():
            assert row['module'] == name
            assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name]
            profiles(row)
            if name in fresh:
                assert len(row['axiom_profiles']) == cell['axiom_profile_counts'][name] == 1
                assert all(row[key] == cell['modules'][name][key] for key in ('source_sha256', 'source_closure_sha256'))
            else:
                assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
                assert identity(name, row) == identity(name, base['modules'][name])
        frontier = read_json('fast40_remaining_frontier.json')
        assert frontier['endpoint'] == cell['endpoint'] and frontier['required_modules'] == 37
        assert frontier['within_bound'] is True and frontier['max_fresh'] == 7
        assert len(frontier['fresh_modules']) == 7 and set(frontier['fresh_modules']) == set(fresh)
        checked = read_json('fast40_remaining_identity_check.json')
        assert checked['status'] == 'FAST40_REMAINING_STAGED_KERNEL_EXPORTS_VERIFIED'
        assert checked['scope_key'] == cell['key'] and checked['endpoint'] == cell['endpoint']
        assert checked['required_modules'] == 37 and checked['fresh_modules'] == 7
        for key in ('original_data_preserved_verbatim', 'public_acceptance_types_preserved',
                    'acceptance_proof_bodies_changed', 'standard_axioms_only'):
            assert checked[key] is True
        declared = sum(archive.getinfo(relative).file_size for name, row in fresh.items()
                       for relative, _, _ in output_members(name, row))
        assert declared <= MAX_OUTPUT
        logical = 0
        for name, row in fresh.items():
            identity(name, row)
            assert read_json(name + '.json') == row
            logical += check_archive_outputs(archive, name, row)
        assert logical == declared == checked['verified_fresh_output_bytes']
        observer = read_json('resource_observer.json')
        assert observer['status'] == 'VERIFIER_COMPLETED' and observer['exit_code'] == 0
        assert observer['mathlib_and_lean_flags_unchanged'] is True
    return fresh, dict(receipt_sha256=hashlib.sha256(receipt_bytes).hexdigest(),
                      required_modules=37, fresh_modules=7, prior_identities_matched=30,
                      verified_fresh_output_bytes=logical, historical_output_equality_claimed=False)


def check_existing(build, fresh):
    for name, row in fresh.items():
        record = build / (name + '.json')
        if record.exists():
            assert identity(name, json.loads(record.read_bytes())) == identity(name, row), ('Conflicting record', name)
        for relative, digest, size in output_members(name, row):
            path = build / relative
            assert path.resolve().is_relative_to(build)
            if path.exists():
                assert path.is_file() and (size is None or path.stat().st_size == size)
                assert digest_file(path) == digest, ('Conflicting existing output', name, relative)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--spec', type=pathlib.Path, default=ROOT / SPEC)
    p.add_argument('--restore', action='store_true')
    p.add_argument('--build-directory', type=pathlib.Path, default=SOURCE / 'build/extension')
    args = p.parse_args()
    spec, base, graph = load_spec(args.spec)
    scopes = {key: source_scope(spec['cell_jobs'][key], base, graph) for key in KEYS}
    repository, run, commit = os.environ['GITHUB_REPOSITORY'], int(os.environ['GITHUB_RUN_ID']), os.environ['GITHUB_SHA']
    assert repository == REPOSITORY and re.fullmatch(r'[0-9a-f]{40}', commit) and run > 0
    api = GitHub(repository)
    current = api.get('/actions/runs/' + str(run))
    assert current['id'] == run and current['head_sha'] == commit and current['path'] == WORKFLOW
    jobs = api.listing('/actions/runs/' + str(run) + '/jobs?filter=all', 'jobs')
    artifacts = api.listing('/actions/runs/' + str(run) + '/artifacts', 'artifacts')
    output = ROOT / 'ci/rg_fast40_remaining_staged_exports' / str(run)
    output.mkdir(parents=True, exist_ok=True)
    build, covered, reports = args.build_directory.resolve(), set(), []
    for key in KEYS:
        cell = spec['cell_jobs'][key]
        job = latest_job(jobs, cell, run, commit)
        artifact_name = cell['artifact_name_template'].format(run=run, attempt=job['run_attempt'])
        matches = [artifact for artifact in artifacts if artifact['name'] == artifact_name]
        assert len(matches) == 1, ('Missing or ambiguous original upload', artifact_name)
        artifact = matches[0]
        assert not artifact['expired'] and 0 < artifact['size_in_bytes'] <= MAX_ZIP
        assert artifact['workflow_run']['id'] == run and artifact['workflow_run']['head_sha'] == commit
        assert re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest'])
        manifest = dict(repository=repository, run=run, job=job['id'], source_commit=commit,
                        artifact_id=artifact['id'], artifact_sha256=artifact['digest'].removeprefix('sha256:'),
                        lean_version=spec['lean_version'], mathlib=PIN, leancert=LC)
        data = fetch_archive(manifest)
        assert len(data) == artifact['size_in_bytes'] and len(data) <= MAX_ZIP
        assert hashlib.sha256(data).hexdigest() == manifest['artifact_sha256']
        with tempfile.TemporaryDirectory(prefix='rg-fast40-staged-cell-') as temporary:
            archive = pathlib.Path(temporary) / 'current-cell.zip'
            archive.write_bytes(data)
            del data
            fresh, audit = authenticate(archive, cell, spec, base, *scopes[key])
            assert not covered & set(fresh)
            covered.update(fresh)
            manifest['modules'] = dict(sorted(fresh.items()))
            manifest['origin_context'] = dict(kind='AUTHENTICATED_NEW_SOURCE_CELL_KERNEL_EXPORT',
                                              spec_sha256=SPEC_SHA256, run_attempt=job['run_attempt'], **audit)
            destination = output / ('cell' + key + '.json')
            destination.write_text(json.dumps(manifest, indent=2) + '\n')
            if args.restore:
                check_existing(build, fresh)
                subprocess.run([sys.executable, '-B', str(ROOT / 'ci/rg_restore_job_exports.py'),
                                '--manifest', str(destination), '--build-directory', str(build),
                                '--verified-local-archive', str(archive)], check=True)
        report = dict(key=key, job=job['id'], artifact_id=artifact['id'], run_attempt=job['run_attempt'], **audit)
        reports.append(report)
        print(json.dumps(dict(status='AUTHENTICATED_STAGED_CELL_EXPORT', **report)), flush=True)
    assert covered == set(spec['all_new_cell_modules']) and len(covered) == 63
    print(json.dumps(dict(status='AUTHENTICATED_NINE_STAGED_CELL_ARCHIVES', run=run, source_commit=commit,
                          spec_sha256=SPEC_SHA256, archives=9, fresh_modules=63, restored=args.restore,
                          proof_scope='NEW_CELL_EXPORTS_ONLY_NO_FAST40_OR_FAMILY_COMPLETION_CLAIM',
                          historical_output_equality_claimed=False, reports=reports)), flush=True)


if __name__ == '__main__':
    main()
