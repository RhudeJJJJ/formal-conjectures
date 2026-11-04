"""Recover exactly two unchanged Middle generic exports; prove no family claim."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
BUILD = SOURCES / 'build/extension'
EXPORTS = SOURCES / 'build/fresh_exports'
SPEC = 'ci/rg_middle_generic_recovery_20261104_spec.json'
SPEC_SHA = '137191ab660e927667aca036c1a5ae49651f5793da26470a4ecc19cc6ea440d7'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ORIGIN_KEYS = ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from rg_plan_exact_degree_one_large import source_closure
from rg_github_rate_limit import api_open


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def bound_json(relative, digest):
    raw = (ROOT / relative).read_bytes()
    assert sha(raw) == digest, ('Changed sealed input', relative)
    return json.loads(raw)


def context():
    spec = bound_json(SPEC, SPEC_SHA)
    for relative, digest in spec['unchanged_helper_sha256'].items():
        assert sha((ROOT / relative).read_bytes()) == digest, ('Changed fixed verifier/helper', relative)
    old_binding, base_binding = spec['original_manifest'], spec['available_base_manifest']
    original = bound_json(old_binding['path'], old_binding['sha256'])
    base = bound_json(base_binding['path'], base_binding['sha256'])
    assert {k: original[k] for k in ORIGIN_KEYS} == old_binding['origin']
    assert original['modules'] == old_binding['module_rows']
    assert {k: base[k] for k in ORIGIN_KEYS} == base_binding['origin']
    assert base['kind'] == 'INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE'
    assert len(base['modules']) == base_binding['complete_capsule_modules'] == 193
    assert base['mathlib'] == original['mathlib'] == spec['mathlib']
    assert base['lean_version'] == original['lean_version'] == spec['lean_version'] == '4.33.1'
    fresh, prior = set(spec['required_fresh_modules']), set(spec['required_prior_modules'])
    assert len(fresh) == 2 and fresh == set(original['modules'])
    assert len(prior) == 46 and not fresh.intersection(base['modules'])
    assert spec['limits'] == dict(workers=1, module_timeout_seconds=600, memory_reserve_mib=2048, max_fresh=2)
    expected = spec['current_source_graph']
    encoded = (json.dumps(expected, indent=2, sort_keys=True) + '\n').encode()
    assert sha(encoded) == spec['current_source_graph_sha256']
    assert all(set(expected[key]) == prior | fresh for key in expected)
    for name in expected['source_sha256']:
        assert (SOURCES / (name.replace('.', '/') + '.lean')).is_file(), ('Missing original source', name)
    hashes, dependencies, closures = source_closure(spec['endpoint'])
    assert dict(source_sha256=hashes, source_dependencies=dependencies,
                source_closure_sha256=closures) == expected, 'Changed full current import closure'
    assert len(hashes) == spec['required_modules'] == 48
    for name in prior | fresh:
        row = original['modules'][name] if name in fresh else base['modules'][name]
        assert row['module'] == name
        assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name], name
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        list(output_members(name, row))
    return spec, original, base


def api(path):
    request = urllib.request.Request('https://api.github.com/repos/RhudeJJJJ/formal-conjectures' + path,
        headers={'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'],
                 'Accept': 'application/vnd.github+json', 'User-Agent': 'rg-exact-middle-generic-recovery'})
    with api_open(request) as response:
        return json.load(response)


def available_base(spec, base):
    catalog = api('/actions/runs/' + str(base['run']) + '/artifacts?per_page=100&page=1')
    assert catalog['total_count'] == len(catalog['artifacts']) <= 100
    matches = [a for a in catalog['artifacts'] if a['id'] == base['artifact_id']]
    assert len(matches) == 1, 'The only permitted base archive is unavailable'
    artifact = matches[0]
    assert artifact['expired'] is False
    assert artifact['digest'] == 'sha256:' + base['artifact_sha256']
    assert artifact['size_in_bytes'] == spec['available_base_manifest']['artifact_size_in_bytes']
    assert artifact['workflow_run']['id'] == base['run']
    assert artifact['workflow_run']['head_sha'] == base['source_commit']
    return catalog


def current_origin(spec):
    assert os.environ['GITHUB_REPOSITORY'] == spec['repository']
    assert os.environ['GITHUB_REF_NAME'] == spec['branch']
    assert os.environ['GITHUB_EVENT_NAME'] == 'push'
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert re.fullmatch(r'[0-9a-f]{40}', commit) and commit == os.environ['GITHUB_SHA']
    return dict(repository=spec['repository'], source_commit=commit,
        run=int(os.environ['GITHUB_RUN_ID']), run_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']))


def prepare(spec, original, base):
    origin = current_origin(spec)
    assert not list(BUILD.glob('Proofs.*.json')) and not (BUILD / 'receipt.json').exists()
    catalog = available_base(spec, base)
    bundle = EXPORTS / 'generated_source'
    for name in spec['current_source_graph']['source_sha256']:
        relative = pathlib.Path('Proofs/RG_Lean_20261019') / (name.replace('.', '/') + '.lean')
        target = bundle / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    report = dict(status='EXACT_48_MODULE_SOURCES_AND_AVAILABLE_BASE_REQUIRES_TWO_FRESH_KERNEL_EXPORTS',
        spec_sha256=SPEC_SHA, current_origin=origin, endpoint=spec['endpoint'], required_modules=48,
        required_prior_modules=spec['required_prior_modules'], required_fresh_modules=spec['required_fresh_modules'],
        current_source_graph=spec['current_source_graph'], actual_base_artifact_catalog=catalog,
        original_manifest_origin=spec['original_manifest']['origin'],
        original_two_module_rows=original['modules'], original_artifact_relabelled_as_available=False,
        kernel_receipt_created=False, full_degree_one_middle_family_claim=False)
    EXPORTS.mkdir(parents=True, exist_ok=True)
    (EXPORTS / 'source_and_base_preflight.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')


def restored_row(base, name):
    old = base['modules'][name]
    if old['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
        origin = old['origin']
    else:
        assert old['mode'] == 'FRESH_KERNEL_EXPORT'
        origin = {key: base[key] for key in ORIGIN_KEYS}
    return dict(old, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=origin,
        transport_capsule={key: base[key] for key in ORIGIN_KEYS if key != 'repository'})


def check_outputs(name, row):
    total = 0
    for relative, digest, size in output_members(name, row):
        path = BUILD / relative
        assert path.resolve().is_relative_to(BUILD.resolve())
        assert path.is_file() and (size is None or path.stat().st_size == size)
        with path.open('rb') as stream:
            assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest, relative
        total += path.stat().st_size
    return total


def check_prior_rows(spec, base):
    for name in spec['required_prior_modules']:
        row = read_json(BUILD / (name + '.json'))
        assert row == restored_row(base, name), ('Changed original prior record', name)
        check_outputs(name, row)


def preflight(spec, original, base):
    actual = read_json(BUILD / 'bounded_kernel_fallback_plan.json')
    assert actual['status'] == 'EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS'
    assert actual['endpoint'] == spec['endpoint'] and actual['required_modules'] == 48
    assert actual['verified_prior_objects'] == 46 and actual['max_fresh'] == 2
    assert actual['within_bound'] is True and set(actual['fresh_modules']) == set(original['modules'])
    assert len(actual['fresh_modules']) == 2
    assert not (BUILD / 'receipt.json').exists()
    for name in original['modules']:
        assert not (BUILD / (name + '.json')).exists()
        assert not (BUILD / (name.replace('.', '/') + '.olean')).exists()
    records = {p.stem: read_json(p) for p in BUILD.glob('Proofs.*.json')}
    assert set(records) == set(base['modules'])
    assert all(row == restored_row(base, name) for name, row in records.items())
    check_prior_rows(spec, base)
    EXPORTS.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(BUILD / 'bounded_kernel_fallback_plan.json', EXPORTS / 'bounded_kernel_fallback_plan.json')


def named_profiles(name, row, spec):
    raw = (BUILD / (name + '.log')).read_bytes()
    text = raw.decode('utf-8')
    assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', text)
    matches = list(re.finditer(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", text, re.S))
    names = [m.group(1) for m in matches]
    assert names == spec['expected_named_axiom_declarations'][name]
    profiles = [sorted(set(x.strip() for x in m.group(2).split(',') if x.strip()))
                if m.group(2) is not None else [] for m in matches]
    assert all(set(profile) <= ALLOWED for profile in profiles)
    grouped = [profiles[i] for i, m in enumerate(matches) if m.group(2) is not None]
    grouped += [profiles[i] for i, m in enumerate(matches) if m.group(2) is None]
    assert grouped == row['axiom_profiles']
    return dict(log_sha256=sha(raw), declarations=dict(zip(names, profiles)))


def verify(spec, original, base):
    origin = current_origin(spec)
    receipt_raw = (BUILD / 'receipt.json').read_bytes()
    receipt = json.loads(receipt_raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [spec['endpoint']]
    assert receipt['mathlib'] == spec['mathlib'] and receipt['leancert'] == spec['leancert']
    assert 'version 4.33.1,' in receipt['lean']
    assert receipt['global_rg'] == 'NOT_PROVED' and receipt['complete_submission'] == 'NOT_SUBMITTED'
    rows = receipt['modules']
    graph = spec['current_source_graph']
    assert set(rows) == set(graph['source_sha256']) and len(rows) == 48
    assert {n for n, r in rows.items() if r['mode'] == 'FRESH_KERNEL_EXPORT'} == set(original['modules'])
    for name, row in rows.items():
        assert row['module'] == name and row['source_sha256'] == graph['source_sha256'][name]
        assert row['source_closure_sha256'] == graph['source_closure_sha256'][name]
        assert row['axiom_profiles'] and all(set(profile) <= ALLOWED for profile in row['axiom_profiles'])
        if name not in original['modules']:
            assert row == restored_row(base, name), ('Changed final prior identity or origin', name)
    check_prior_rows(spec, base)
    comparisons = {}
    for name, old in original['modules'].items():
        row = rows[name]
        assert row == read_json(BUILD / (name + '.json')) and row['mode'] == 'FRESH_KERNEL_EXPORT'
        assert 'origin' not in row and 'transport_capsule' not in row
        for key in ('source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
            assert row[key] == old[key], ('Rebuilt original identity differs', name, key)
        assert row.get('additional_outputs', {}) == old.get('additional_outputs', {})
        comparisons[name] = dict(original_identity=old, actual_fresh_export=row,
            source_identical=True, closure_identical=True, output_identical=True,
            output_bytes_verified=check_outputs(name, row), named_profile_audit=named_profiles(name, row, spec))
    diagnostics = {p.stem: read_json(p) for p in BUILD.glob('Proofs.*.json')}
    assert set(diagnostics) == set(base['modules']) | set(original['modules'])
    assert {n for n, row in diagnostics.items() if row['mode'] == 'FRESH_KERNEL_EXPORT'} == set(original['modules'])
    assert sum(len(r['named_profile_audit']['declarations']) for r in comparisons.values()) == 3
    resource = read_json(EXPORTS / 'resource_observer.json')
    assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == 0
    assert resource['mathlib_and_lean_flags_unchanged'] is True
    report = dict(status='EXACT_TWO_ORIGINAL_MIDDLE_GENERIC_EXPORTS_REBUILT_BY_CURRENT_KERNEL',
        spec_sha256=SPEC_SHA, current_origin=origin, endpoint=spec['endpoint'], required_modules=48,
        prior_modules=46, fresh_modules=sorted(original['modules']), named_axiom_profiles=3,
        receipt_sha256=sha(receipt_raw), current_source_graph_sha256=spec['current_source_graph_sha256'],
        original_manifest_origin=spec['original_manifest']['origin'],
        actual_fresh_exports_are_new_origin=True, unavailable_old_artifact_relabelled_as_available=False,
        comparisons=comparisons, preserved_base_transport=spec['available_base_manifest']['origin'],
        full_degree_one_middle_family_claim=False, global_rg_claim=False)
    (EXPORTS / 'original_identity_comparison.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'endpoint', 'required_modules', 'prior_modules', 'fresh_modules', 'named_axiom_profiles')}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('prepare', 'preflight', 'verify'), required=True)
    args = parser.parse_args()
    spec, original, base = context()
    globals()[args.phase](spec, original, base)


if __name__ == '__main__':
    main()
