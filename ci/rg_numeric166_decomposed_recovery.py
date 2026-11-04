"""Recheck four original leaves in bounded modules, then join all ten endpoints.

The six old endpoint objects keep their authenticated original origin. Every
declaration in the four remaining leaves is retained verbatim in twenty modules.
Four independent jobs export actual kernel objects. The final job authenticates
their exact origins, restores them, and requires a zero-fresh 160-module receipt.
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
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
BUILD = SOURCES / 'build/extension'
EXPORTS = SOURCES / 'build/fresh_exports'
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from verify import without_comments
from rg_original_d1_numeric_reproduction import load_plan
from rg_plan_exact_degree_one_large import source_closure
from rg_d1_numeric_remainder import load_remainder, identity, partial_origin

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
WORKFLOW = '.github/workflows/rg-d1-numeric166-decomposed-recovery-20261104.yml'
SPEC = 'ci/rg_d1_numeric166_decomposed_20261104_spec.json'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MASTER_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
KEYS = tuple(f'{i:05d}' for i in range(1666, 1670))
ENDPOINTS = [f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in range(1660, 1670)]
LABELS = ['Base'] + [f'Outer{i:02d}' for i in range(8)] + ['Affine'] + [f'Rows{i:02d}' for i in range(9)] + ['']
NEW = {name + label for name in ENDPOINTS[6:] for label in LABELS}
NS = 'Gebendorfer.RadenkovicGutman.DegreeOneLongClass00'
MAX_JSON = 32 * 1024 ** 2
MAX_ZIP = 1024 ** 3
MAX_OUTPUT = 2 * 1024 ** 3
AXIOM_VALIDATION = {
    'kind': 'NAMED_CURRENT_LOGS_REASSEMBLED_IN_ORIGINAL_VERIFIER_ORDER',
    'current_module_names': 'EXACT_ORIGINAL_SNAPSHOT_PRINT_NAMES_IN_SOURCE_ORDER',
    'record_normalization': 'NONEMPTY_PROFILES_IN_PRINT_ORDER_THEN_EMPTY_PROFILES',
    'complete_original_profile_array_match_required': True,
    'historical_name_to_profile_mapping_inferred': False,
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def digest_file(path):
    with pathlib.Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def bound_file(relative, digest):
    path = pathlib.PurePosixPath(relative)
    assert path.is_relative_to('ci') and '..' not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == digest, ('Changed sealed input', relative)
    return json.loads(raw)


def context(spec_sha):
    spec = bound_file(SPEC, spec_sha)
    assert spec['kind'] == 'SOURCE_PRESERVING_NUMERIC166_FULL_BATCH_WITH_PRESERVED_PARTIAL_ORIGINS'
    assert spec['batch_id'] == '00_166' and spec['endpoints'] == ENDPOINTS
    assert spec['original_master_source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert spec['mathlib'] == PIN and spec['leancert'] == LC and spec['lean_version'] == '4.33.1'
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib'], spec['max_parallel_leaf_jobs']) == (1, 1200, 2048, 2)
    assert spec['original_master_spec_sha256'] == MASTER_SHA
    master = bound_file(spec['original_master_spec'], MASTER_SHA)
    assert len(master['scheduled_numeric_modules']) == len(set(master['scheduled_numeric_modules'])) == 4567
    planned = [p for p in master['jobs'] if p['batch'] == '00_166']
    assert len(planned) == 1
    assert spec['original_plan'] == planned[0]['plan'] and spec['original_plan_sha256'] == planned[0]['plan_sha256']
    bound_file(spec['original_plan'], spec['original_plan_sha256'])
    bound_file(spec['legacy_remainder_spec'], spec['legacy_remainder_spec_sha256'])
    legacy, plan, expected, partial = load_remainder('00_166')
    assert legacy == bound_file(spec['legacy_remainder_spec'], spec['legacy_remainder_spec_sha256'])
    assert plan['endpoints'] == ENDPOINTS and set(expected) == set(ENDPOINTS)
    assert spec['base_manifest'] == plan['base_manifest'] and spec['base_manifest_sha256'] == plan['base_manifest_sha256']
    base = bound_file(spec['base_manifest'], spec['base_manifest_sha256'])
    assert spec['partial_manifest'] == legacy['partial_manifest'] and spec['partial_manifest_sha256'] == legacy['partial_manifest_sha256']
    assert partial == bound_file(spec['partial_manifest'], spec['partial_manifest_sha256'])
    assert set(partial['modules']) == set(ENDPOINTS[:6])
    snapshots = bound_file(spec['original_source_snapshot'], spec['original_source_snapshot_sha256'])
    assert set(snapshots) == set(KEYS)
    assert spec['source_reorganized_original_modules'] == ENDPOINTS[6:]
    assert spec['historical_unchanged_numeric_modules'] == ENDPOINTS[:6]
    assert set(spec['added_support_modules']) == NEW - set(ENDPOINTS)
    assert set(spec['new_source_exports']) == set(spec['modules']) == NEW
    assert spec['proof_bodies_changed'] is False and spec['original_declarations_preserved_verbatim'] is True
    assert (spec['original_definitions'], spec['original_theorems'], spec['original_axiom_prints']) == (532, 1252, 1252)
    assert (spec['required_module_count'], spec['prior_module_count'], spec['fresh_module_count']) == (160, 80, 80)
    assert spec['original_numeric_module_count'] == 10
    assert spec['axiom_profile_validation'] == AXIOM_VALIDATION
    assert len(spec['required_modules']) == len(set(spec['required_modules'])) == 160
    assert set(spec['required_source_sha256']) == set(spec['required_source_closure_sha256']) == set(spec['required_modules'])
    assert set(spec['required_modules']) - set(base['modules']) - set(partial['modules']) == NEW
    assert set(spec['leaf_jobs']) == set(KEYS)
    for key in KEYS:
        leaf = spec['leaf_jobs'][key]
        endpoint = 'Proofs.RadenkovicGutmanD1Long00Leaf' + key
        assert leaf['key'] == key and leaf['endpoint'] == endpoint
        assert leaf['job_name'] == 'numeric166-leaf-' + key
        assert leaf['artifact_name_template'] == 'rg-d1-numeric166-leaf-' + key + '-{run}-{attempt}'
        assert leaf['required_success_step'] == 'Authenticate the complete original leaf and all current output bytes'
        assert (leaf['required_module_count'], leaf['prior_module_count'], leaf['fresh_module_count']) == (94, 74, 20)
        assert set(leaf['modules']) == {endpoint + label for label in LABELS}
        assert len(leaf['modules']) == 20 and len(leaf['required_modules']) == len(set(leaf['required_modules'])) == 94
        assert set(leaf['required_modules']) - set(base['modules']) == set(leaf['modules'])
    return spec, plan, expected, base, partial, snapshots


def preserve_declarations(spec, expected, snapshots):
    for key in KEYS:
        snapshot = snapshots[key]
        name = 'Proofs.RadenkovicGutmanD1Long00Leaf' + key
        original = snapshot['source']
        assert snapshot['kind'] == 'ORIGINAL_NUMERIC166_DECLARATION_SOURCE_REFERENCE'
        assert snapshot['original_module'] == name
        assert snapshot['original_source_commit'] == spec['original_master_source_commit']
        assert sha(original.encode()) == snapshot['original_source_sha256'] == expected[name]['source_sha256']
        assert snapshot['header'] + snapshot['body'] + snapshot['footer'] == original
        assert snapshot['imports'] + snapshot['context'] == snapshot['header']
        assert snapshot['namespace'] == NS and snapshot['footer'] == 'end ' + NS + '\n'
        parts = snapshot['parts']
        assert [p['label'] for p in parts] == LABELS
        assert {p['module'] for p in parts} == set(spec['leaf_jobs'][key]['modules'])
        offset = count = 0
        declarations = []
        for part in parts:
            module = part['module']
            assert module == name + part['label'] and part['start'] == offset and part['end'] > offset
            block = snapshot['body'][offset:part['end']]
            assert sha(block.encode()) == part['body_sha256']
            assert len(re.findall(r'^def ', block, re.M)) == part['definitions']
            assert len(re.findall(r'^theorem ', block, re.M)) == part['theorems']
            prints = re.findall(r'^#print axioms (.+)$', block, re.M)
            assert prints == part['axiom_declarations'] and prints
            assert set(part['additional_imports']) <= set(spec['leaf_jobs'][key]['modules']) - {module}
            raw = (snapshot['imports'] + ''.join('import ' + n + '\n' for n in part['additional_imports'])
                   + part['docstring'] + snapshot['context'] + block + snapshot['footer']).encode()
            actual = (SOURCES / (module.replace('.', '/') + '.lean')).read_bytes()
            assert actual == raw and sha(actual) == spec['modules'][module]['source_sha256']
            assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', without_comments(actual.decode()), re.M)
            assert 'axiom_profiles' not in spec['modules'][module]
            assert spec['modules'][module]['axiom_profile_count'] == len(prints)
            offset = part['end']
            count += len(prints)
            declarations.extend(prints)
        assert offset == len(snapshot['body']) and count == 313
        assert declarations == re.findall(r'^#print axioms (.+)$', snapshot['body'], re.M)
        assert len(declarations) == len(set(declarations)) == len(expected[name]['axiom_profiles']) == 313
        assert sum(p['definitions'] for p in parts) == 133 and sum(p['theorems'] for p in parts) == 313
        assert '#print axioms leaf' + key + '_checked\n' in snapshot['body'][parts[-1]['start']:]


def materialize_unchanged(spec, expected, snapshots):
    producer = bound_file(spec['producer_plan'], spec['producer_plan_sha256'])
    for relative, digest in producer['producer_source_sha256'].items():
        p = pathlib.PurePosixPath(relative)
        assert p.is_relative_to('ci') and '..' not in p.parts and digest_file(ROOT / p) == digest
    entry = producer['classes']['00']
    assert 166 in entry['open_chunk_indices']
    p = pathlib.PurePosixPath(entry['packet'])
    assert not p.is_absolute() and '..' not in p.parts
    raw = (ROOT / p).read_bytes()
    assert sha(raw) == entry['packet_sha256']
    packet = json.loads(raw)
    from rg_shared_arm_common import module
    from rg_shared_arm_source import body
    leaves = []
    def walk(node):
        if node['kind'] in ('first', 'second'):
            walk(node['left']); walk(node['right'])
        else:
            assert node['kind'] == 'polynomial'
            leaves.append(node)
    for cell in packet['cells']:
        walk(cell['tree'])
    assert len(leaves) == entry['leaf_count']
    for index in range(1660, 1670):
        name = f'Proofs.RadenkovicGutmanD1Long00Leaf{index:05d}'
        imports, text = body('00', index, leaves[index], shared_weights=True)
        raw = module('DegreeOneLongClass00', imports, text).encode()
        assert sha(raw) == expected[name]['source_sha256']
        if index >= 1666:
            assert raw == snapshots[f'{index:05d}']['source'].encode()
        else:
            path = SOURCES / (name.replace('.', '/') + '.lean')
            if path.exists():
                assert path.read_bytes() == raw, ('Changed unchanged original leaf', name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)


def source_scope(spec, expected, base, partial):
    hashes, closures = {}, {}
    for endpoint in ENDPOINTS:
        h, _, c = source_closure(endpoint)
        hashes.update(h); closures.update(c)
    assert hashes == spec['required_source_sha256'] and closures == spec['required_source_closure_sha256']
    assert len(hashes) == 160
    for name, row in spec['modules'].items():
        assert hashes[name] == row['source_sha256'] and closures[name] == row['source_closure_sha256']
        assert 'axiom_profiles' not in row and row['axiom_profile_count'] > 0
    for name in set(hashes) - NEW:
        old = partial['modules'].get(name, base['modules'].get(name))
        assert old is not None and hashes[name] == old['source_sha256'] and closures[name] == old['source_closure_sha256']
        if name in partial['modules']:
            assert identity(name, old) == identity(name, expected[name])
    for key in KEYS:
        leaf = spec['leaf_jobs'][key]
        h, _, c = source_closure(leaf['endpoint'])
        assert set(h) == set(leaf['required_modules'])
        assert h == {n: hashes[n] for n in h} and c == {n: closures[n] for n in c}
    return hashes, closures


def verifier_profile_order(profiles):
    return [p for p in profiles if p] + [[] for p in profiles if not p]


def named_log_profiles(raw, expected_names):
    assert isinstance(raw, bytes) and len(raw) <= MAX_JSON
    text = raw.decode()
    assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', text)
    pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
    parsed = []
    for match in pattern.finditer(text):
        name, used, empty = match.groups()
        profile = [] if empty else sorted(set(x.strip() for x in used.split(',') if x.strip()))
        assert empty or profile
        assert set(profile) <= ALLOWED, ('Unexpected axiom', name, profile)
        parsed.append((name, profile))
    assert [n for n, _ in parsed] == expected_names and len(expected_names) == len(set(expected_names))
    return parsed


def validate_named_split_axioms(spec, original_rows, snapshot, rows, read_module_log):
    assert spec['axiom_profile_validation'] == AXIOM_VALIDATION
    all_pairs, counts = [], {}
    for part in snapshot['parts']:
        name = part['module']; row = rows[name]
        assert row['module'] == name
        for k in ('source_sha256', 'source_closure_sha256'):
            assert row[k] == spec['modules'][name][k]
        names = [snapshot['namespace'] + '.' + n for n in part['axiom_declarations']]
        pairs = named_log_profiles(read_module_log(name), names)
        assert len(pairs) == spec['modules'][name]['axiom_profile_count']
        assert row['axiom_profiles'] == verifier_profile_order([p for _, p in pairs])
        all_pairs.extend(pairs); counts[name] = len(pairs)
    printed = [snapshot['namespace'] + '.' + n for n in re.findall(r'^#print axioms (.+)$', snapshot['body'], re.M)]
    assert len(all_pairs) == len({n for n, _ in all_pairs}) == 313
    assert [n for n, _ in all_pairs] == printed
    original = original_rows[snapshot['original_module']]['axiom_profiles']
    assert verifier_profile_order([p for _, p in all_pairs]) == original
    return dict(status='CURRENT_NAMED_PROFILES_AND_COMPLETE_ORIGINAL_PROFILE_ARRAY_MATCH',
        original_module=snapshot['original_module'], original_declarations=313, current_modules=20,
        normalization=AXIOM_VALIDATION['record_normalization'], historical_name_to_profile_mapping_inferred=False,
        per_module_profile_counts=counts, current_named_profiles=dict(all_pairs),
        historical_normalized_profile_sha256=sha(json.dumps(original, separators=(',', ':')).encode()))


def profiles(row):
    assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])


def base_origin(base, name):
    row = base['modules'][name]
    if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
        return row['origin']
    assert row['mode'] == 'FRESH_KERNEL_EXPORT'
    return {k: base[k] for k in ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')}


def validate_leaf_receipt(spec, expected, base, snapshot, receipt_raw,
                          read_record, read_log, open_member, member_size):
    key = snapshot['original_module'][-5:]
    leaf = spec['leaf_jobs'][key]
    receipt = json.loads(receipt_raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [leaf['endpoint']]
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC and 'version 4.33.1,' in receipt['lean']
    rows = receipt['modules']
    assert set(rows) == set(leaf['required_modules']) and len(rows) == 94
    fresh = {n: r for n, r in rows.items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert set(fresh) == set(leaf['modules']) and len(fresh) == 20
    for name, row in rows.items():
        assert row['module'] == name
        assert row['source_sha256'] == spec['required_source_sha256'][name]
        assert row['source_closure_sha256'] == spec['required_source_closure_sha256'][name]
        profiles(row)
        if name not in fresh:
            assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            assert identity(name, row) == identity(name, base['modules'][name])
            assert row['origin'] == base_origin(base, name)
    named = validate_named_split_axioms(spec, expected, snapshot, rows, read_log)
    logical = 0
    for name, row in fresh.items():
        assert row == json.loads(read_record(name + '.json'))
        assert 0 < row['seconds'] <= 1200
        for relative, digest, size in output_members(name, row):
            p = pathlib.PurePosixPath(relative)
            assert not p.is_absolute() and '..' not in p.parts
            actual_size = member_size(relative)
            assert size is None or actual_size == size
            logical += actual_size
            assert logical <= MAX_OUTPUT
            with open_member(relative) as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
    return fresh, dict(status='COMPLETE_ORIGINAL_LEAF_DECLARATION_SPLIT_KERNEL_VERIFIED',
        key=key, endpoint=leaf['endpoint'], required_modules=94, fresh_modules=20, prior_modules=74,
        receipt_sha256=sha(receipt_raw), verified_fresh_output_bytes=logical,
        original_declarations_preserved_verbatim=True, proof_bodies_changed=False,
        original_definitions=133, original_theorems=313, standard_axioms_only=True,
        named_axiom_audit=named, historical_object_equality_claimed=False)


def check_resource(observer, fresh_count):
    assert observer['status'] == 'VERIFIER_COMPLETED' and observer['exit_code'] == 0
    assert observer['mathlib_and_lean_flags_unchanged'] is True
    assert observer['samples']
    assert all(s['available_bytes'] >= 2048 * 1024 ** 2 for s in observer['samples'])
    assert max(len(s['lean_processes']) for s in observer['samples']) <= 1
    if not fresh_count:
        # The strict verifier may briefly invoke `lean --version`. A sampled
        # Lean process with no input module is not a fresh compilation.
        assert all(p['module'] is None for s in observer['samples'] for p in s['lean_processes'])


def authenticate_leaf(archive_path, key, spec, expected, base, snapshot):
    assert key in KEYS and snapshot['original_module'].endswith(key)
    assert 0 < archive_path.stat().st_size <= MAX_ZIP
    with zipfile.ZipFile(archive_path) as archive:
        names = archive.namelist()
        assert len(names) == len(set(names)) <= 4096
        for info in archive.infolist():
            p = pathlib.PurePosixPath(info.filename)
            assert not p.is_absolute() and '..' not in p.parts
            assert (info.external_attr >> 16) & 0o170000 != 0o120000
        def small(name):
            assert archive.getinfo(name).file_size <= MAX_JSON
            return archive.read(name)
        receipt_raw = small('receipt.json')
        fresh, audit = validate_leaf_receipt(spec, expected, base, snapshot, receipt_raw,
            small, lambda n: small(n + '.log'), archive.open, lambda p: archive.getinfo(p).file_size)
        archived_names = {p[:-5] for p in names if p.startswith('Proofs.') and p.endswith('.json')}
        assert archived_names == set(fresh)
        saved = json.loads(small('numeric166_leaf_verified.json'))
        assert {k: saved[k] for k in audit} == audit
        assert saved['spec_sha256'] == sha((ROOT / SPEC).read_bytes())
        check_resource(json.loads(small('resource_observer.json')), 20)
    return fresh, audit


class GitHub:
    def __init__(self):
        from rg_github_rate_limit import api_open
        self.open = api_open
        self.base = 'https://api.github.com/repos/' + REPOSITORY
        self.headers = {'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'],
                        'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'}

    def get(self, suffix):
        with self.open(urllib.request.Request(self.base + suffix, headers=self.headers)) as response:
            return json.load(response)

    def listing(self, suffix, member):
        rows = []
        for page in range(1, 101):
            separator = '&' if '?' in suffix else '?'
            data = self.get(suffix + separator + 'per_page=100&page=' + str(page))
            current = data[member]; rows.extend(current)
            assert len({r['id'] for r in rows}) == len(rows)
            if len(rows) == data['total_count']:
                return rows
            assert len(current) == 100 and len(rows) < data['total_count']
        raise AssertionError('Bounded GitHub pagination exceeded')


def check_current_job(jobs, leaf, run, commit):
    matches = [j for j in jobs if j['name'] == leaf['job_name']]
    assert matches and all(j['run_id'] == run and j['head_sha'] == commit for j in matches)
    attempt = max(j['run_attempt'] for j in matches)
    matches = [j for j in matches if j['run_attempt'] == attempt]
    assert len(matches) == 1
    job = matches[0]
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    steps = [s for s in job['steps'] if s['name'] == leaf['required_success_step']]
    assert len(steps) == 1 and steps[0]['status'] == 'completed' and steps[0]['conclusion'] == 'success'
    return job


def origin_descriptor(manifest):
    return {k: manifest[k] for k in ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256', 'artifact_name')}


def collect_leaves(spec, expected, base, snapshots, spec_sha):
    from rg_github_artifacts import fetch_archive
    run, commit = int(os.environ['GITHUB_RUN_ID']), os.environ['GITHUB_SHA']
    assert os.environ['GITHUB_REPOSITORY'] == REPOSITORY and run > 0 and re.fullmatch(r'[0-9a-f]{40}', commit)
    api = GitHub(); metadata = api.get('/actions/runs/' + str(run))
    assert metadata['id'] == run and metadata['head_sha'] == commit and metadata['path'] == WORKFLOW
    jobs = api.listing('/actions/runs/' + str(run) + '/jobs?filter=all', 'jobs')
    artifacts = api.listing('/actions/runs/' + str(run) + '/artifacts', 'artifacts')
    manifests, audits, covered = {}, {}, set()
    directory = ROOT / 'ci/rg_numeric166_decomposed_exports' / str(run)
    directory.mkdir(parents=True, exist_ok=True)
    for key in KEYS:
        leaf = spec['leaf_jobs'][key]
        job = check_current_job(jobs, leaf, run, commit)
        artifact_name = leaf['artifact_name_template'].format(run=run, attempt=job['run_attempt'])
        matches = [a for a in artifacts if a['name'] == artifact_name]
        assert len(matches) == 1
        artifact = matches[0]
        assert not artifact['expired'] and 0 < artifact['size_in_bytes'] <= MAX_ZIP
        assert artifact['workflow_run']['id'] == run and artifact['workflow_run']['head_sha'] == commit
        assert re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest'])
        manifest = dict(repository=REPOSITORY, run=run, job=job['id'], source_commit=commit,
            artifact_id=artifact['id'], artifact_sha256=artifact['digest'].removeprefix('sha256:'),
            artifact_name=artifact_name, lean_version='4.33.1', mathlib=PIN, leancert=LC)
        raw = fetch_archive(manifest)
        assert len(raw) == artifact['size_in_bytes'] and sha(raw) == manifest['artifact_sha256']
        with tempfile.TemporaryDirectory(prefix='rg-numeric166-leaf-') as temporary:
            path = pathlib.Path(temporary) / 'leaf.zip'; path.write_bytes(raw); del raw
            fresh, audit = authenticate_leaf(path, key, spec, expected, base, snapshots[key])
            assert not covered & set(fresh)
            covered.update(fresh)
            manifest['modules'] = dict(sorted(fresh.items()))
            manifest['origin_context'] = dict(kind='AUTHENTICATED_DECLARATION_PRESERVING_ORIGINAL_NUMERIC166_LEAF',
                key=key, spec_sha256=spec_sha, run_attempt=job['run_attempt'],
                receipt_sha256=audit['receipt_sha256'], required_modules=94, fresh_modules=20,
                original_definitions=133, original_theorems=313,
                named_profile_sha256=sha(json.dumps(audit['named_axiom_audit'], separators=(',', ':')).encode()))
            target = directory / ('leaf' + key + '.json'); save(target, manifest)
            for name, row in fresh.items():
                existing = BUILD / (name + '.json')
                if existing.exists():
                    assert identity(name, json.loads(existing.read_bytes())) == identity(name, row)
            subprocess.run([sys.executable, '-B', 'ci/rg_restore_job_exports.py',
                '--manifest', str(target), '--build-directory', str(BUILD), '--verified-local-archive', str(path)], cwd=ROOT, check=True)
        manifests[key] = manifest; audits[key] = audit
        print(json.dumps(dict(status='AUTHENTICATED_NUMERIC166_LEAF_ORIGIN', key=key,
            job=job['id'], artifact_id=artifact['id'], fresh_modules=20)), flush=True)
    assert covered == NEW and len(covered) == 80
    save(EXPORTS / 'numeric166_leaf_manifests.json', manifests)
    save(EXPORTS / 'named_profile_audits.json', {k: a['named_axiom_audit'] for k, a in audits.items()})
    save(EXPORTS / 'numeric166_leaf_audits.json', audits)


def check_zero_receipt(spec, expected, base, partial, manifests, receipt_raw):
    receipt = json.loads(receipt_raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == ENDPOINTS
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC and 'version 4.33.1,' in receipt['lean']
    rows = receipt['modules']
    assert set(rows) == set(spec['required_modules']) and len(rows) == 160
    assert set(manifests) == set(KEYS)
    fresh_origins = {}
    for key, manifest in manifests.items():
        assert set(manifest['modules']) == set(spec['leaf_jobs'][key]['modules'])
        for name, row in manifest['modules'].items():
            assert name not in fresh_origins and row['mode'] == 'FRESH_KERNEL_EXPORT'
            fresh_origins[name] = (row, partial_origin(manifest))
    assert set(fresh_origins) == NEW
    for name, row in rows.items():
        assert row['module'] == name and row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
        assert row['source_sha256'] == spec['required_source_sha256'][name]
        assert row['source_closure_sha256'] == spec['required_source_closure_sha256'][name]
        profiles(row)
        if name in fresh_origins:
            old, origin = fresh_origins[name]
            assert identity(name, row) == identity(name, old) and row['origin'] == origin
        elif name in partial['modules']:
            assert identity(name, row) == identity(name, partial['modules'][name]) == identity(name, expected[name])
            assert row['origin'] == partial_origin(partial)
        else:
            assert identity(name, row) == identity(name, base['modules'][name])
            assert row['origin'] == base_origin(base, name)
    return dict(status='NUMERIC166_COMPLETE_ZERO_FRESH_RECEIPT_METADATA_CHECKED',
        required_modules=160, fresh_modules=0, restored_prior_modules=160,
        original_endpoints=ENDPOINTS, preserved_original_endpoint_objects=6,
        source_reorganized_original_endpoint_modules=ENDPOINTS[6:], added_support_modules=76,
        actual_compiled_leaf_modules=80, compiled_leaf_origins={k: origin_descriptor(manifests[k]) for k in KEYS},
        original_partial_origin=partial_origin(partial),
        old_failed_job_status='UNCHANGED_FAILURE', prior_records_relabelled_as_fresh=False,
        receipt_sha256=sha(receipt_raw),
        original_declarations_preserved_verbatim=True, proof_bodies_changed=False,
        standard_axioms_only=True, original_definitions=532, original_theorems=1252,
        full_degree_one_large_closure='PENDING_SEPARATE_FINAL_ASSEMBLY')


def validate_complete_receipt(spec, expected, base, partial, receipt_raw, manifests,
                              read_record, open_member, member_size):
    report = check_zero_receipt(spec, expected, base, partial, manifests, receipt_raw)
    rows = json.loads(receipt_raw)['modules']
    logical = 0
    for name, row in rows.items():
        assert row == json.loads(read_record(name + '.json'))
        # Recheck all selected original endpoint and split output bytes. The
        # unchanged strict verifier independently checks the entire 160 scope.
        if name in NEW or name in partial['modules']:
            for relative, digest, size in output_members(name, row):
                p = pathlib.PurePosixPath(relative)
                assert not p.is_absolute() and '..' not in p.parts
                actual = member_size(relative)
                assert size is None or actual == size
                logical += actual
                assert logical <= 8 * 1024 ** 3
                with open_member(relative) as stream:
                    assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
    report.update(status='COMPLETE_ORIGINAL_NUMERIC166_BATCH_WITH_DECLARATION_PRESERVING_SPLITS',
                  verified_original_and_current_output_bytes=logical)
    return report


def local(relative):
    p = pathlib.PurePosixPath(relative)
    assert not p.is_absolute() and '..' not in p.parts
    path = BUILD / p
    assert path.resolve().is_relative_to(BUILD.resolve())
    return path


def preflight(endpoints, expected_fresh):
    observed = set()
    frontiers = []
    for endpoint in endpoints:
        subprocess.run([sys.executable, '-B', 'ci/rg_restore_with_kernel_fallback.py',
            '--plan', 'ci/rg_empty_restore_plan.json', '--build-directory', str(BUILD),
            '--endpoint', endpoint, '--max-fresh', str(len(expected_fresh)), '--preflight-only'], cwd=ROOT, check=True)
        frontier = json.loads((BUILD / 'bounded_kernel_fallback_plan.json').read_bytes())
        assert frontier['endpoint'] == endpoint and frontier['within_bound'] is True
        assert set(frontier['fresh_modules']) <= expected_fresh
        observed.update(frontier['fresh_modules'])
        frontiers.append(frontier)
    assert observed == expected_fresh
    return frontiers


def kernel(endpoints):
    command = [sys.executable, '-B', 'ci/rg_observed_kernel_verify.py', '--memory-reserve-mib', '2048',
               '--', '--mathlib-project', str(ROOT)]
    for endpoint in endpoints:
        command.extend(['--endpoint', endpoint])
    command.extend(['--workers', '1', '--module-timeout', '1200', '--resume'])
    subprocess.run(command, cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec-sha256', required=True)
    parser.add_argument('--leaf', choices=KEYS)
    parser.add_argument('--phase', choices=('materialize', 'cache', 'preflight', 'kernel', 'compare',
                                          'collect', 'join-preflight', 'join-kernel', 'join-compare'), required=True)
    args = parser.parse_args()
    spec, plan, expected, base, partial, snapshots = context(args.spec_sha256)
    preserve_declarations(spec, expected, snapshots)
    if args.phase == 'materialize':
        materialize_unchanged(spec, expected, snapshots)
        preserve_declarations(spec, expected, snapshots)
    source_scope(spec, expected, base, partial)
    EXPORTS.mkdir(parents=True, exist_ok=True)
    if args.phase in ('preflight', 'kernel', 'compare'):
        assert args.leaf is not None
        leaf = spec['leaf_jobs'][args.leaf]
    if args.phase == 'materialize':
        print(json.dumps(dict(status='EXACT_TEN_ORIGINAL_ENDPOINTS_AND_FOUR_DECLARATION_SPLITS_BOUND_NO_KERNEL_PROOF',
            required_modules=160, original_declarations_preserved_verbatim=True, fresh_leaf_modules=80)), flush=True)
    elif args.phase == 'cache':
        subprocess.run([sys.executable, '-B', 'ci/rg_run_original_d1_numeric.py',
                        '--plan', spec['original_plan'], '--phase', 'cache'], cwd=ROOT, check=True)
    elif args.phase == 'preflight':
        preflight([leaf['endpoint']], set(leaf['modules']))
    elif args.phase == 'kernel':
        kernel([leaf['endpoint']])
    elif args.phase == 'compare':
        fresh, audit = validate_leaf_receipt(spec, expected, base, snapshots[args.leaf],
            (BUILD / 'receipt.json').read_bytes(), lambda p: local(p).read_bytes(),
            lambda n: local(n + '.log').read_bytes(), lambda p: local(p).open('rb'), lambda p: local(p).stat().st_size)
        check_resource(json.loads((EXPORTS / 'resource_observer.json').read_bytes()), 20)
        audit.update(spec_sha256=args.spec_sha256, source_commit=os.environ['GITHUB_SHA'],
            workflow_run=int(os.environ['GITHUB_RUN_ID']), workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']))
        save(EXPORTS / 'numeric166_leaf_verified.json', audit)
        print(json.dumps({k: v for k, v in audit.items() if k != 'named_axiom_audit'}), flush=True)
    elif args.phase == 'collect':
        collect_leaves(spec, expected, base, snapshots, args.spec_sha256)
    elif args.phase == 'join-preflight':
        frontiers = preflight(ENDPOINTS, set())
        save(EXPORTS / 'numeric166_join_frontier.json', dict(
            status='COMPLETE_ORIGINAL_NUMERIC166_ZERO_FRESH_FRONTIER_BOUND_NO_NEW_KERNEL_PROOF',
            endpoints=ENDPOINTS, required_modules=160, fresh_modules=[], frontiers=frontiers))
    elif args.phase == 'join-kernel':
        kernel(ENDPOINTS)
    else:
        manifests = json.loads((EXPORTS / 'numeric166_leaf_manifests.json').read_bytes())
        audit = validate_complete_receipt(spec, expected, base, partial, (BUILD / 'receipt.json').read_bytes(), manifests,
            lambda p: local(p).read_bytes(), lambda p: local(p).open('rb'), lambda p: local(p).stat().st_size)
        check_resource(json.loads((EXPORTS / 'resource_observer.json').read_bytes()), 0)
        audit.update(spec_sha256=args.spec_sha256, source_commit=os.environ['GITHUB_SHA'],
            workflow_run=int(os.environ['GITHUB_RUN_ID']), workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
            named_profile_audits_sha256=digest_file(EXPORTS / 'named_profile_audits.json'),
            leaf_manifests_sha256=digest_file(EXPORTS / 'numeric166_leaf_manifests.json'))
        save(EXPORTS / 'numeric166_complete_verified.json', audit)
        print(json.dumps(audit), flush=True)


if __name__ == '__main__':
    main()
