"""Check the exact staged Bernstein factorization of the original Ge46 proof.

Proposed integer rows are never certificates by assumption: each row's exact
coefficient identity and Hybrid acceptance must be ordinary kernel exports.
Every stage has a fixed complete source scope and an exact fresh frontier.
"""
import argparse, hashlib, io, json, os, pathlib, re, shutil, subprocess, sys, zipfile
from rg_plan_exact_degree_one_large import source_closure, without_comments
from rg_collect_exact_d1_reproductions import GitHub, identity, latest_named_job, records_from_log
from rg_github_artifacts import fetch_archive

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Proofs/RG_Lean_20261019'
BUILD = SOURCE / 'build/extension'
EXPORTS = SOURCE / 'build/fresh_exports'
sys.path.insert(0, str(SOURCE))
from module_outputs import output_members

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
STEM = 'Proofs.RadenkovicGutmanEscapeReducedReserve'
HELPER = 'Proofs.RadenkovicGutmanIntegerHybridBernsteinRows'
ENDPOINT = 'Proofs.RadenkovicGutmanOriginalDegreeGeFortysix'
SPEC = ROOT / 'ci/rg_ge46_checked_rows_20261103_spec.json'
STAGE_KEYS = {'prepare', 'evaluation', 'final'} | {f'row{i:02d}' for i in range(24)}
NEW_SOURCES = {STEM, STEM + 'Data', STEM + 'Acceptance', STEM + 'Evaluation', HELPER} | {
    STEM + f'Row{i:02d}' for i in range(25)}


CURRENT_ACCEPTED_PROFILE_METADATA = {'kind': 'TWO_EXACT_CURRENT_SOURCE_LOCATIONS_OF_THE_SAME_ACCEPTED_DECLARATION', 'affected_declaration': 'Gebendorfer.RadenkovicGutman.EscapeReducedReserve.accepted', 'historical_accepted_axioms': ['propext'], 'current_accepted_axioms': ['Classical.choice', 'Quot.sound', 'propext'], 'modules': {'Proofs.RadenkovicGutmanEscapeReducedReserveAcceptance': {'source_sha256': 'e855c5a92d39e85fdb8145a052bdf441a465ac1f7459aa97f7298b5e435493c8', 'source_closure_sha256': 'f591d1dde62db6315e11e627fceb9cae3b17fe1b8f1cad9d4897ce0bf5a5a603', 'printed_declarations': ['Gebendorfer.RadenkovicGutman.EscapeReducedReserve.accepted'], 'axiom_profiles': [['Classical.choice', 'Quot.sound', 'propext']]}, 'Proofs.RadenkovicGutmanEscapeReducedReserve': {'source_sha256': '26135477ffa18dc9b30dea9bcff99ebb8f64027ea1a8736fb5833a11f7fdedbc', 'source_closure_sha256': '24e30a209c0e9ce6630b4871f77f69901fce0fe226b183c206881b383ab4da45', 'printed_declarations': ['Gebendorfer.RadenkovicGutman.EscapeReducedReserve.accepted', 'Gebendorfer.RadenkovicGutman.EscapeReducedReserve.unit_box_nonneg', 'Gebendorfer.RadenkovicGutman.EscapeReducedReserve.data_eval'], 'axiom_profiles': [['Classical.choice', 'Quot.sound', 'propext'], ['Classical.choice', 'Quot.sound', 'propext'], ['Classical.choice', 'Quot.sound', 'propext']]}}, 'all_other_historical_profiles_and_output_identity_gates_unchanged': True}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound(relative, digest):
    path = pathlib.PurePosixPath(relative)
    assert path.is_relative_to('ci') and '..' not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == digest, ('Changed sealed reference', relative)
    return json.loads(raw)


def preserve_declarations(declarations):
    assert declarations['kind'] == 'EXACT_ORIGINAL_ESCAPE_DECLARATIONS_WITH_CHECKED_ROWS'
    assert declarations['original_source_sha256'] == 'cafecd99d1755286e6fe6d5b31614e993502a2d63eecb1ce6df1d8cb2f1a05e2'
    assert declarations['original_source_commit'] == '4ab5802ec7da33fcb4a54633e2e7c9863c974244'
    assert declarations['degrees'] == [24, 28, 4, 4] and declarations['outer_rows'] == list(range(25))
    assert set(declarations['exact_source_sha256']) == NEW_SOURCES
    texts = {}
    for name, digest in declarations['exact_source_sha256'].items():
        raw = (SOURCE / (name.replace('.', '/') + '.lean')).read_bytes()
        assert sha(raw) == digest, ('Changed candidate source', name)
        text = raw.decode()
        code = without_comments(text)
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^\s*axiom\s', code, re.M), name
        texts[name] = text
    data = re.search(r'^noncomputable def data : NestedInteger\.Poly 4 := .*\n', texts[STEM + 'Data'], re.M)[0]
    degrees = re.search(r'^def degrees : Fin 4 → ℕ := .*\n', texts[STEM + 'Data'], re.M)[0]
    accepted_type = re.search(r'^theorem accepted : .*?(?=:=)', texts[STEM + 'Acceptance'], re.M)[0]
    unit_box = re.search(r'^theorem unit_box_nonneg .*?(?=\n#print axioms accepted)', texts[STEM], re.M | re.S)[0]
    evaluation = re.search(r'^theorem data_eval .*?(?=\n#print axioms data_eval)', texts[STEM + 'Evaluation'], re.M | re.S)[0]
    blocks = dict(data=data, degrees=degrees, accepted_type=accepted_type,
                  unit_box_nonneg=unit_box, data_eval=evaluation)
    for key, text in blocks.items():
        assert sha(text.encode()) == declarations['original_declaration_sha256'][key], ('Changed original declaration', key)
    assert accepted_type.strip() == declarations['original_acceptance_type']


def load_spec():
    spec = json.loads(SPEC.read_bytes())
    assert spec['kind'] == 'EXACT_ORIGINAL_GE46_CHECKED_BERNSTEIN_ROWS'
    assert spec['mathlib'] == PIN and spec['leancert'] == LC and spec['lean_version'] == '4.33.1'
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (1, 1200, 2048)
    assert spec['endpoint'] == ENDPOINT and spec['required_module_count'] == 178
    assert spec['current_accepted_profile_metadata'] == CURRENT_ACCEPTED_PROFILE_METADATA
    assert set(spec['stages']) == STAGE_KEYS and spec['new_and_recompiled_module_count'] == 91
    assert set(spec['stages']['prepare']['fresh_modules']) == {STEM + 'Data', STEM + 'Row24', HELPER}
    for j in range(24):
        assert set(spec['stages'][f'row{j:02d}']['fresh_modules']) == {STEM + 'Data', STEM + f'Row{j:02d}'}
    assert set(spec['stages']['evaluation']['fresh_modules']) == {STEM + 'Data', STEM + 'Evaluation'}
    assert spec['stages']['final']['fresh_module_count'] == 63
    assert set(spec['stages']['final']['prerequisites']) == STAGE_KEYS - {'final'}
    for stage in spec['stages'].values():
        assert stage['endpoints'] == sorted(set(stage['endpoints']))
        assert stage['required_modules'] == sorted(set(stage['required_modules']))
        assert stage['fresh_modules'] == sorted(set(stage['fresh_modules']))
        assert len(stage['fresh_modules']) == stage['fresh_module_count']
        assert len(stage['required_modules']) == stage['required_module_count']
        assert stage['required_success_step'] == 'Require exact original declarations and staged kernel exports'
    base = bound(spec['base_manifest'], spec['base_manifest_sha256'])
    partial = bound(spec['partial_manifest'], spec['partial_manifest_sha256'])
    historical = bound(spec['historical_reference'], spec['historical_reference_sha256'])
    declarations = bound(spec['declarations_manifest'], spec['declarations_manifest_sha256'])
    assert len(base['modules']) == 193 and len(partial['modules']) == 5
    assert not set(base['modules']) & set(partial['modules'])
    preserve_declarations(declarations)
    return spec, historical


def current_scope(spec, stage):
    hashes, closures = {}, {}
    for endpoint in stage['endpoints']:
        h, _, c = source_closure(endpoint)
        hashes.update(h)
        closures.update(c)
    assert set(hashes) == set(stage['required_modules'])
    for name in hashes:
        expected = spec['source_graph'][name]
        assert (hashes[name], closures[name]) == (expected['source_sha256'], expected['source_closure_sha256']), name
    if ENDPOINT in hashes:
        assert hashes[ENDPOINT] == spec['original_public_family_source_sha256'], 'Original public family source changed'
    return hashes, closures


def checked_local_path(relative):
    path = pathlib.PurePosixPath(relative)
    assert not path.is_absolute() and '..' not in path.parts
    actual = BUILD / path
    assert actual.resolve().is_relative_to(BUILD.resolve()), ('Local output escapes build directory', relative)
    return actual


def validate_current_accepted_profiles(spec, historical, name, row, read_module_log):
    """Bind only the two reviewed observations of the changed accepted proof."""
    assert spec['current_accepted_profile_metadata'] == CURRENT_ACCEPTED_PROFILE_METADATA
    policy = CURRENT_ACCEPTED_PROFILE_METADATA['modules'][name]
    assert row['module'] == name
    for key in ('source_sha256', 'source_closure_sha256'):
        assert row[key] == policy[key] == spec['source_graph'][name][key]
    old = historical['modules'][STEM]['axiom_profiles']
    standard = ['Classical.choice', 'Quot.sound', 'propext']
    assert old == [['propext'], standard, standard]
    assert row['axiom_profiles'] == policy['axiom_profiles']
    raw = read_module_log(name)
    assert isinstance(raw, bytes) and len(raw) <= 32 * 1024**2
    text = raw.decode('utf-8')
    assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', text)
    pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
    pairs = []
    for match in pattern.finditer(text):
        declaration, used, empty = match.groups()
        profile = [] if empty else sorted(set(x.strip() for x in used.split(',') if x.strip()))
        assert set(profile) <= ALLOWED
        pairs.append((declaration, profile))
    assert [declaration for declaration, _ in pairs] == policy['printed_declarations']
    assert [profile for _, profile in pairs] == policy['axiom_profiles']
    assert pairs[0] == (CURRENT_ACCEPTED_PROFILE_METADATA['affected_declaration'], standard)
    if name == STEM:
        assert [profile for _, profile in pairs[1:]] == old[1:]
    return dict(module=name, source_sha256=row['source_sha256'],
        source_closure_sha256=row['source_closure_sha256'],
        named_profiles=dict(pairs), old_accepted_axioms=['propext'],
        current_accepted_axioms=standard, all_other_original_profiles_unchanged=True)


def check_receipt(spec, historical, stage, raw, read_record, open_member, member_size, read_module_log):
    receipt = json.loads(raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == stage['endpoints']
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC and 'version 4.33.1,' in receipt['lean']
    assert set(receipt['modules']) == set(stage['required_modules'])
    for name, row in receipt['modules'].items():
        expected = spec['source_graph'][name]
        assert row['module'] == name
        assert row['source_sha256'] == expected['source_sha256']
        assert row['source_closure_sha256'] == expected['source_closure_sha256']
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        assert row['mode'] in ('FRESH_KERNEL_EXPORT', 'PRIOR_VERIFIED_JOB_EXPORT')
    fresh = {n:r for n,r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert set(fresh) == set(stage['fresh_modules'])
    logical = 0
    for name, row in fresh.items():
        assert row == json.loads(read_record(name + '.json')), ('Archived row differs', name)
        old = historical['modules'].get(name)
        if old is not None:
            same_source = (row['source_sha256'], row['source_closure_sha256']) == (old['source_sha256'], old['source_closure_sha256'])
            assert spec['source_graph'][name]['require_historical_output_identity'] == same_source
            if name in CURRENT_ACCEPTED_PROFILE_METADATA['modules']:
                assert not same_source, 'No unchanged source may use a current-profile exception'
            else:
                assert row['axiom_profiles'] == old['axiom_profiles'], ('Changed original axiom footprint', name)
            if same_source:
                assert identity(name, row) == identity(name, old), ('Changed historical output identity', name)
        if name in CURRENT_ACCEPTED_PROFILE_METADATA['modules']:
            validate_current_accepted_profiles(spec, historical, name, row, read_module_log)
        elif name == STEM + 'Evaluation':
            assert row['axiom_profiles'] == [historical['modules'][STEM]['axiom_profiles'][2]]
        for relative, digest, size in output_members(name, row):
            path = pathlib.PurePosixPath(relative)
            assert not path.is_absolute() and '..' not in path.parts
            actual_size = member_size(relative)
            assert size is None or size == actual_size
            with open_member(relative) as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest, (name, relative)
            logical += actual_size
    assert logical <= 8 * 1024**3
    return fresh, logical, sha(raw)


def restore_parents(spec, historical, stage):
    assert stage['prerequisites']
    repository = os.environ['GITHUB_REPOSITORY']
    run, commit = int(os.environ['GITHUB_RUN_ID']), os.environ['GITHUB_SHA']
    assert repository == 'RhudeJJJJ/formal-conjectures'
    api = GitHub(repository)
    actual = api.get('/actions/runs/' + str(run))
    assert actual['head_sha'] == commit and actual['head_branch'] == 'rg-degree-one-large-20261103'
    assert actual['path'] == '.github/workflows/rg-ge46-checked-rows-reconstruction-20261103.yml'
    jobs = api.listing('/actions/runs/' + str(run) + '/jobs?filter=all', 'jobs')
    artifacts = api.listing('/actions/runs/' + str(run) + '/artifacts', 'artifacts')
    output = SOURCE / 'build/ge46_checked_rows_parent_exports'
    output.mkdir(parents=True, exist_ok=True)
    covered, reports = {}, []
    total = 0
    for key in stage['prerequisites']:
        parent = spec['stages'][key]
        current_scope(spec, parent)
        job = latest_named_job(jobs, parent['job_name'])
        assert job['run_id'] == run and job['head_sha'] == commit
        assert job['status'] == 'completed' and job['conclusion'] == 'success'
        checks = [s for s in job['steps'] if s['name'] == parent['required_success_step']]
        assert len(checks) == 1 and checks[0]['conclusion'] == 'success'
        name = parent['artifact_name_template'].format(run=run, attempt=job['run_attempt'])
        matches = [a for a in artifacts if a['name'] == name]
        assert len(matches) == 1
        artifact = matches[0]
        assert not artifact['expired'] and artifact['workflow_run']['id'] == run
        assert artifact['workflow_run']['head_sha'] == commit
        assert re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest'])
        assert artifact['size_in_bytes'] <= 1024**3
        manifest = dict(repository=repository, run=run, job=job['id'], source_commit=commit,
            artifact_id=artifact['id'], artifact_sha256=artifact['digest'][7:], lean_version='4.33.1', mathlib=PIN)
        archive_raw = fetch_archive(manifest)
        assert len(archive_raw) == artifact['size_in_bytes']
        with zipfile.ZipFile(io.BytesIO(archive_raw)) as z:
            names = z.namelist()
            assert len(names) == len(set(names))
            for info in z.infolist():
                p = pathlib.PurePosixPath(info.filename)
                assert not p.is_absolute() and '..' not in p.parts
                assert (info.external_attr >> 16) & 0o170000 != 0o120000
            fresh, logical, receipt_sha = check_receipt(spec, historical, parent,
                z.read('receipt.json'), z.read, z.open, lambda n: z.getinfo(n).file_size,
                lambda name: z.read(name + '.log'))
            logged = records_from_log(api.logs(job['id']))
            assert fresh == logged, ('Fresh job log differs from actual archived receipt', key)
            selected = {}
            selected_bytes = 0
            for n, row in fresh.items():
                if n in covered:
                    assert identity(n, covered[n]) == identity(n, row), ('Conflicting shared source/object identity', n)
                else:
                    covered[n] = row
                    selected[n] = row
                    selected_bytes += sum(z.getinfo(rel).file_size for rel, _, _ in output_members(n, row))
        total += selected_bytes
        assert total <= 2 * 1024**3, 'Explicit staged-parent object budget exceeded'
        assert shutil.disk_usage(ROOT).free >= 8 * 1024**3 + 2 * selected_bytes
        manifest['modules'] = selected
        manifest['origin_context'] = dict(kind='ACTUAL_COMPLETE_STAGED_KERNEL_EXPORT', stage=key,
            complete_original_fresh_frontier=parent['fresh_modules'], receipt_sha256=receipt_sha,
            entire_fresh_archive_authenticated_before_identical_shared_row_projection=True)
        archive_path = output / (key + '.zip')
        manifest_path = output / (key + '_prior_exports.json')
        archive_path.write_bytes(archive_raw)
        manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
        subprocess.run([sys.executable, '-B', 'ci/rg_restore_job_exports.py',
            '--manifest', str(manifest_path), '--verified-local-archive', str(archive_path),
            '--build-directory', str(BUILD)], cwd=ROOT, check=True)
        archive_path.unlink()
        reports.append(dict(stage=key, run=run, job=job['id'], artifact_id=artifact['id'],
            full_fresh_modules=len(fresh), restored_unique_modules=len(selected), original_output_bytes=logical))
        print(json.dumps(reports[-1]), flush=True)
    expected = set().union(*(set(spec['stages'][k]['fresh_modules']) for k in stage['prerequisites']))
    assert set(covered) == expected and len(covered) == 28
    (output / 'collection.json').write_text(json.dumps(dict(
        status='ALL28STAGED_PARENT_MODULES_AUTHENTICATED_NOT_A_NEW_KERNEL_RUN',
        unique_modules=len(covered), original_output_bytes=total, stages=reports), indent=2) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage', choices=sorted(STAGE_KEYS), required=True)
    p.add_argument('--phase', choices=('source', 'cache', 'restore', 'before', 'kernel', 'after'), required=True)
    a = p.parse_args()
    spec, historical = load_spec()
    stage = spec['stages'][a.stage]
    hashes, closures = current_scope(spec, stage)
    EXPORTS.mkdir(parents=True, exist_ok=True)
    if a.phase == 'source':
        report = dict(status='EXACT_STAGED_SOURCE_ONLY_NO_KERNEL_PROOF', stage=a.stage,
            required_modules=len(hashes), expected_fresh_modules=stage['fresh_modules'])
    elif a.phase == 'cache':
        external = set()
        for name in hashes:
            directory = SOURCE / 'ThirdParty/LeanCert' if name.startswith('LeanCert.') else SOURCE
            code = without_comments((directory / (name.replace('.', '/') + '.lean')).read_text())
            for dependency in re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)\s*$', code, re.M):
                if not dependency.startswith(('Proofs.', 'LeanCert.', 'Lean.', 'Init.', 'Std.')) and dependency not in ('Lean', 'Init', 'Std'):
                    external.add(dependency)
        subprocess.run(['lake', 'exe', 'cache', 'get', *sorted(external)], cwd=ROOT, check=True)
        return
    elif a.phase == 'restore':
        restore_parents(spec, historical, stage)
        return
    elif a.phase == 'before':
        fresh, frontiers = set(), []
        for endpoint in stage['endpoints']:
            subprocess.run([sys.executable, '-B', 'ci/rg_restore_with_kernel_fallback.py',
                '--plan', 'ci/rg_empty_restore_plan.json', '--build-directory', str(BUILD),
                '--endpoint', endpoint, '--max-fresh', str(stage['fresh_module_count']), '--preflight-only'], cwd=ROOT, check=True)
            frontier = json.loads((BUILD / 'bounded_kernel_fallback_plan.json').read_bytes())
            assert frontier['within_bound'] is True
            assert set(frontier['fresh_modules']) <= set(stage['fresh_modules'])
            fresh.update(frontier['fresh_modules'])
            frontiers.append(frontier)
        assert fresh == set(stage['fresh_modules'])
        report = dict(status='EXACT_STAGED_FRONTIER_ONLY_NO_KERNEL_PROOF', stage=a.stage,
            required_modules=len(hashes), fresh_modules=sorted(fresh), frontiers=frontiers)
    elif a.phase == 'kernel':
        command = [sys.executable, '-B', 'ci/rg_observed_kernel_verify.py',
            '--memory-reserve-mib', '2048', '--', '--mathlib-project', str(ROOT)]
        for endpoint in stage['endpoints']:
            command.extend(['--endpoint', endpoint])
        command.extend(['--workers', '1', '--module-timeout', '1200', '--resume'])
        subprocess.run(command, cwd=ROOT, check=True)
        return
    else:
        fresh, logical, receipt_sha = check_receipt(spec, historical, stage,
            checked_local_path('receipt.json').read_bytes(), lambda n: checked_local_path(n).read_bytes(),
            lambda n: checked_local_path(n).open('rb'), lambda n: checked_local_path(n).stat().st_size,
            lambda name: checked_local_path(name + '.log').read_bytes())
        report = dict(status='EXACT_STAGED_KERNEL_EXPORTS_VERIFIED', stage=a.stage,
            endpoints=stage['endpoints'], required_modules=len(hashes), fresh_modules=sorted(fresh),
            receipt_sha256=receipt_sha, original_output_bytes=logical,
            original_public_declarations_preserved=True, whole_degree_one_large='NOT_CLAIMED_BY_THIS_STAGE')
    (EXPORTS / ('ge46_checked_rows_' + a.phase + '.json')).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'frontiers'}), flush=True)


if __name__ == '__main__':
    main()
