"""Bind successful original reconstruction jobs to exact final restore manifests.

No logged record substitutes for a binary proof. The subsequent compressed
restore must authenticate the complete original ZIP, archived row, every output
member and current recursive source closure. Named auxiliary workflows are
bound either to explicit historical runs or the exact publishing commit.
"""
import argparse, hashlib, json, os, pathlib, re, sys, time
import urllib.error, urllib.parse, urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
sys.path.insert(0, str(SOURCES))
from rg_github_rate_limit import api_open
from module_outputs import output_members
from rg_plan_exact_degree_one_large import source_closure

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NUMERIC137_ZERO_AUDIT = 'NUMERIC137_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT'
NUMERIC137_COMPLETIONS = {'DECLARATION_PRESERVING_ORIGINAL137_FULL_BATCH', NUMERIC137_ZERO_AUDIT}
NUMERIC166_JOIN = 'NUMERIC166_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_BATCH_JOIN'
NUMERIC_REORGANIZED_COMPLETIONS = NUMERIC137_COMPLETIONS | {NUMERIC166_JOIN}
REFERENCE_COMPLETION = 'EXACT_REGISTERED_REFERENCE_BATCH_COMPLETION'
THREE_WAVE_TWO_COMPLETION = 'EXACT_REGISTERED_THREE_WAVE_TWO_BATCH_COMPLETION'
NEW_WRAPPERS = {
    'Proofs.RadenkovicGutmanCompactFiniteDegreeOneSmallCertificatesComplete',
    'Proofs.RadenkovicGutmanCompactFiniteOriginalDegreeOneSmall',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound_file(relative, digest):
    p = pathlib.Path(relative)
    assert p.is_relative_to('ci') and '..' not in p.parts
    raw = (ROOT / p).read_bytes()
    assert sha(raw) == digest, relative
    return json.loads(raw)


def original_rows(item):
    if item.get('expected_kind') == 'GE46_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT':
        from rg_ge46_zero_fresh_completion import completion_context
        return completion_context(item)['proof']['modules']
    if item.get('expected_kind') == 'existing_compact_small_ge_four_scope':
        assert item['endpoint'] == 'Proofs.RadenkovicGutmanCompactFiniteOriginalSmallGeFour'
        assert set(item['audit_source']) == {'source_sha256', 'source_closure_sha256'}
        return {}
    if item.get('expected_kind') == 'new_compact_wrappers':
        rows = item['modules']
        assert set(rows) == NEW_WRAPPERS, 'Only the two sealed original compact wrappers may be first exports'
        assert all(set(r) == {'source_sha256', 'source_closure_sha256'} for r in rows.values())
        return rows
    manifests = {p: bound_file(p, h) for p, h in item['original_manifests'].items()}
    rows = {}
    for name, relative in item['fresh_module_origins'].items():
        manifest = manifests[relative]
        assert manifest['mathlib'] == PIN and manifest['lean_version'] == '4.33.1'
        table = manifest['historical_rows'] if manifest.get('kind') == 'EXACT_COMPACT_CLOSED_ORIGINAL_SUPPORT_RECONSTRUCTION' else manifest['modules']
        row = table[name]
        assert row['module'] == name
        if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
            assert manifest.get('kind') == 'HISTORICAL_GE46_IDENTITIES_NOT_A_RESTORABLE_ARCHIVE'
            origin = row['origin']
            assert set(origin) == {'repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256'}
            assert origin['repository'] == 'RhudeJJJJ/formal-conjectures'
            assert all(isinstance(origin[k], int) and origin[k] > 0 for k in ('run', 'job', 'artifact_id'))
            assert re.fullmatch(r'[0-9a-f]{40}', origin['source_commit'])
            assert re.fullmatch(r'[0-9a-f]{64}', origin['artifact_sha256'])
        else: assert row['mode'] == 'FRESH_KERNEL_EXPORT'
        rows[name] = row
    assert rows
    return rows


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
            data = self.get(suffix + separator + 'per_page=100&page=' + str(page))
            current = data[member]
            rows.extend(current)
            assert len({r['id'] for r in rows}) == len(rows)
            if len(rows) == data['total_count']: return rows
            assert len(current) == 100 and len(rows) < data['total_count']
        raise AssertionError('Bounded GitHub pagination limit exceeded')

    def logs(self, job):
        class NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, *args, **kwargs): return None
        request = urllib.request.Request(self.base + '/actions/jobs/' + str(job) + '/logs', headers=self.headers)
        try:
            with api_open(request, urllib.request.build_opener(NoRedirect).open) as response:
                return response.read()
        except urllib.error.HTTPError as error:
            assert error.code in (301, 302, 303, 307, 308)
            target = error.headers['Location']
            parsed = urllib.parse.urlparse(target)
            assert parsed.scheme == 'https' and parsed.hostname and not parsed.username and not parsed.password
            # GitHub credentials never follow the signed storage redirect.
            with urllib.request.urlopen(target, timeout=120) as response: return response.read()


def records_from_log(raw):
    records = {}
    for line in raw.decode('utf-8').splitlines():
        marker = 'COMPLETED_MODULE_JSON '
        if marker not in line: continue
        payload = line.split(marker, 1)[1]
        if not payload.startswith('{'): continue
        row = json.loads(payload)
        if row['mode'] != 'FRESH_KERNEL_EXPORT': continue
        name = row['module']
        assert name not in records or records[name] == row, ('Conflicting logged export', name)
        records[name] = row
    return records


def identity(name, row):
    return (row['source_sha256'], row['source_closure_sha256'], row['output_sha256'],
            row['axiom_profiles'], tuple(sorted(output_members(name, row))))


def compare_records(fresh, expected, hashes, closures, first_exports=False):
    assert set(fresh) == set(expected), ('Unexpected fresh reconstruction frontier',
        sorted(set(fresh) - set(expected)), sorted(set(expected) - set(fresh)))
    if first_exports: assert set(fresh) == NEW_WRAPPERS
    for name, row in fresh.items():
        old = expected[name]
        assert row['module'] == name
        assert row['source_sha256'] == hashes[name] == old['source_sha256'], name
        assert row['source_closure_sha256'] == closures[name] == old['source_closure_sha256'], name
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles']), name
        list(output_members(name, row))
        if not first_exports: assert identity(name, row) == identity(name, old), ('Historical object identity differs', name)


def latest_named_job(jobs, name):
    matches = [j for j in jobs if j['name'] == name]
    assert matches, ('No exact named job', name)
    attempt = max(j['run_attempt'] for j in matches)
    matches = [j for j in matches if j['run_attempt'] == attempt]
    assert len(matches) == 1, ('Ambiguous named job attempt', name, attempt)
    return matches[0]


def reference_completion_binding(item, spec_raw, origin):
    """Bind the fixed exact-reference run without inventing an original result.

    This is a complete reproduction of an unchanged batch, not a failed-job
    repair. Its original-job observation is context only; the successful
    reference job, exact records and complete archive remain mandatory.
    """
    assert item['provenance_kind'] == REFERENCE_COMPLETION
    assert not {'original_job', 'original_job_lookup', 'completion_kind'} & item.keys()
    assert origin['repository'] == 'RhudeJJJJ/formal-conjectures'
    assert origin['run'] == 41686621300
    assert origin['source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert sha(spec_raw) == 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
    plans = {p['batch']: p for p in json.loads(spec_raw)['jobs']}
    registry = bound_file('ci/rg_d1_original_reference_bytes_20261103.json',
        'a04e5e612ce5e927a9f121a03b2786224b84736e64cee1974eaaa8c603693dc9')
    registered = registry['affected_numeric_batches']
    assert len(registered) == len(set(registered)) == 186
    assert set(registered) <= plans.keys() and item['batch'] in registered
    plan = plans[item['batch']]
    assert item['original_plan_sha256'] == plan['plan_sha256']
    assert all(type(item[k]) is int and item[k] > 0 for k in ('run', 'job', 'artifact_id'))
    assert item['run'] == 41708676694
    assert item['source_commit'] == 'c2e2f145a77c2c2c65349085283f5ca2db7aa814'
    assert item['workflow_path'] == '.github/workflows/rg-d1-long-reference-recovery-20261103.yml'
    assert item['job_name'] == 'reproduce-original-long-' + item['batch']
    assert item['required_success_step'] == 'Require exact historical output identities'
    assert item['artifact_name'] == 'rg-d1-long-reference-recovery-20261103-41708676694-1-' + item['batch']
    observation = item['original_job_observation']
    assert set(observation) == {'run', 'source_commit', 'run_attempt', 'job_name',
                               'job', 'status', 'conclusion'}
    assert type(observation['run']) is int and observation['run'] == origin['run']
    assert observation['source_commit'] == origin['source_commit']
    assert type(observation['run_attempt']) is int and observation['run_attempt'] == 1
    assert observation['job_name'] == 'original-numeric-' + item['batch']
    if observation['status'] == 'not_created':
        assert plan['wave'] == 2
        assert observation['job'] is None and observation['conclusion'] is None
    else:
        assert type(observation['job']) is int and observation['job'] > 0
        assert observation['status'] in ('queued', 'waiting', 'in_progress', 'completed')
        if observation['status'] == 'completed':
            assert observation['conclusion'] in ('success', 'failure', 'timed_out',
                'cancelled', 'skipped', 'neutral', 'action_required', 'stale', 'startup_failure')
        else:
            assert observation['conclusion'] is None
    return observation


def observe_reference_original_job(item, spec_raw, origin, jobs):
    """Reobserve complete original-job pagination; never require its failure."""
    captured = reference_completion_binding(item, spec_raw, origin)
    matches = [j for j in jobs if j['name'] == captured['job_name']]
    assert len(matches) <= 1, ('Ambiguous original reference-batch job', item['batch'])
    if not matches:
        assert captured['status'] == 'not_created', 'Previously observed original job disappeared'
        return dict(captured)
    job = matches[0]
    assert type(job['id']) is int and job['id'] > 0
    assert job['run_id'] == captured['run'] and job['head_sha'] == captured['source_commit']
    assert type(job['run_attempt']) is int and job['run_attempt'] == 1
    assert job['head_branch'] == 'rg-degree-one-large-20261103'
    if captured['job'] is not None:
        assert job['id'] == captured['job'], 'Original job identity changed'
    observed = dict(captured, job=job['id'], status=job['status'], conclusion=job['conclusion'])
    reference_completion_binding(dict(item, original_job_observation=observed), spec_raw, origin)
    return observed


def original_job_binding(item, spec_raw, origin):
    """Only late original wave-two identities may be resolved from actual jobs.

    Every successful replacement still has a concrete run, job and archive.
    This narrow lookup never supplies an original conclusion or proof object.
    """
    if 'provenance_kind' in item:
        if item['provenance_kind'] == REFERENCE_COMPLETION:
            reference_completion_binding(item, spec_raw, origin)
        else:
            assert item['provenance_kind'] == THREE_WAVE_TWO_COMPLETION
            from rg_actual_numeric_completions import three_binding
            three_binding(item, spec_raw, origin, ROOT)
        return None
    if 'original_job_lookup' not in item:
        assert type(item['original_job']) is int and item['original_job'] > 0
        return None
    assert 'original_job' not in item and 'completion_kind' not in item
    assert origin['run'] == 41686621300
    assert origin['source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert sha(spec_raw) == 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
    spec = json.loads(spec_raw)
    wave_two = {b['batch'] for b in spec['jobs'] if b['wave'] == 2}
    assert len(wave_two) == 93 and item['batch'] in wave_two
    registry = bound_file('ci/rg_d1_original_reference_bytes_20261103.json',
        'a04e5e612ce5e927a9f121a03b2786224b84736e64cee1974eaaa8c603693dc9')
    assert item['batch'] in registry['affected_numeric_batches']
    assert item['run'] == 41708676694
    assert item['source_commit'] == 'c2e2f145a77c2c2c65349085283f5ca2db7aa814'
    assert item['workflow_path'] == '.github/workflows/rg-d1-long-reference-recovery-20261103.yml'
    lookup = item['original_job_lookup']
    assert lookup == {
        'kind': 'EXACT_ORIGINAL_WAVE_TWO_JOB_IN_PINNED_RUN',
        'run': 41686621300,
        'source_commit': 'aaeaec3cec22467d3f0b83b1761bfb40087bb991',
        'run_attempt': 1,
        'job_name': 'original-numeric-' + item['batch'],
    }
    assert type(lookup['run']) is int and type(lookup['run_attempt']) is int
    return lookup


def resolve_original_job(item, spec_raw, origin, jobs):
    lookup = original_job_binding(item, spec_raw, origin)
    assert lookup is not None
    matches = [j for j in jobs if j['name'] == lookup['job_name']]
    assert len(matches) == 1, ('Original wave-two job absent or ambiguous', item['batch'])
    job = matches[0]
    assert type(job['id']) is int and job['id'] > 0
    assert job['run_id'] == lookup['run'] and job['head_sha'] == lookup['source_commit']
    assert type(job['run_attempt']) is int and job['run_attempt'] == lookup['run_attempt']
    assert job['status'] == 'completed' and job['conclusion'] in ('failure', 'timed_out')
    return job


def sealed_numeric_replacements(path, spec_raw, origin, repository):
    """Bind complete origins; repairs keep failed originals, scopes never change."""
    if path is None:
        return {}, None
    raw = path.read_bytes()
    sealed = json.loads(raw)
    assert sealed['kind'] in (
        'SEALED_SUCCESSFUL_ORIGINAL_NUMERIC_BATCH_REPLACEMENTS',
        'SEALED_SUCCESSFUL_NUMERIC_BATCH_COMPLETIONS_WITH_EXPLICIT_SOURCE_REORGANIZATION')
    assert sealed['repository'] == repository
    assert sealed['numeric_run'] == origin['run']
    assert sealed['numeric_source_commit'] == origin['source_commit']
    assert sealed['numeric_spec_sha256'] == sha(spec_raw)
    replacements = {}
    for item in sealed['replacements']:
        required = {
            'batch', 'original_job', 'original_plan_sha256', 'run', 'job',
            'source_commit', 'artifact_id', 'artifact_sha256', 'artifact_name',
            'job_name', 'workflow_path', 'required_success_step',
        }
        if 'completion_kind' in item:
            required |= {'completion_kind', 'completion_spec'}
            if item['completion_kind'] == NUMERIC137_ZERO_AUDIT:
                required.add('compiled_proof_origin')
            if item['completion_kind'] == NUMERIC166_JOIN:
                required |= {'compiled_leaf_origins', 'completion_join_spec'}
        if 'original_job_lookup' in item:
            required = (required - {'original_job'}) | {'original_job_lookup'}
        if 'provenance_kind' in item:
            required = (required - {'original_job'}) | {'provenance_kind', 'original_job_observation'}
        assert set(item) == required, 'A replacement may bind origins, never override the original proof scope'
        assert item['batch'] not in replacements
        original_job_binding(item, spec_raw, origin)
        assert re.fullmatch(r'[0-9a-f]{64}', item['original_plan_sha256'])
        assert all(isinstance(item[k], int) and item[k] > 0 for k in ('run', 'job', 'artifact_id'))
        assert item['run'] != origin['run']
        assert re.fullmatch(r'[0-9a-f]{40}', item['source_commit'])
        assert re.fullmatch(r'[0-9a-f]{64}', item['artifact_sha256'])
        assert isinstance(item['artifact_name'], str) and item['artifact_name']
        assert isinstance(item['job_name'], str) and item['job_name']
        workflow = pathlib.PurePosixPath(item['workflow_path'])
        assert workflow.parent == pathlib.PurePosixPath('.github/workflows') and workflow.suffix == '.yml'
        if 'completion_kind' in item:
            from rg_exact_numeric_completion import completion_context
            completion_context(item)
        else:
            assert item['required_success_step'] == 'Require exact historical output identities'
        replacements[item['batch']] = item
    assert replacements, 'A sealed replacement file must identify actual successful replacement jobs'
    reorganized = [i for i in replacements.values()
                   if i.get('completion_kind') in NUMERIC_REORGANIZED_COMPLETIONS]
    assert bool(reorganized) == (sealed['kind'] ==
        'SEALED_SUCCESSFUL_NUMERIC_BATCH_COMPLETIONS_WITH_EXPLICIT_SOURCE_REORGANIZATION')
    assert {i['batch'] for i in reorganized} <= {'00_137', '00_166'}
    assert len(reorganized) <= 2
    if 'coverage_at_sealing' in sealed:
        from rg_numeric_alternative_coverage import REGISTRY, validate
        validate(sealed['coverage_at_sealing'], spec_raw,
                 (ROOT / REGISTRY).read_bytes(), replacements)
    return replacements, sha(raw)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--spec', type=pathlib.Path, required=True)
    p.add_argument('--external-contract', type=pathlib.Path, required=True)
    p.add_argument('--output', type=pathlib.Path, required=True)
    p.add_argument('--numeric-origin', type=pathlib.Path)
    p.add_argument('--numeric-replacements', type=pathlib.Path)
    p.add_argument('--current-source-binding', type=pathlib.Path)
    p.add_argument('--external-wait-seconds', type=int, default=7200)
    a = p.parse_args()
    assert 0 <= a.external_wait_seconds <= 10800
    spec_raw = a.spec.read_bytes()
    spec = json.loads(spec_raw)
    assert spec['kind'] == 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES'
    assert spec['mathlib'] == PIN and spec['leancert'] == LC
    contract = json.loads(a.external_contract.read_bytes())
    assert contract['kind'] == 'SEALED_D1_COMPLETION_PREREQUISITES'
    current_binding = None
    if a.current_source_binding:
        assert a.numeric_origin, 'Revised sources require the immutable original numeric origin'
        from rg_exact_final_source_binding import (read_binding, prepare_current_sources,
            validate_current_graph, validate_contract_binding)
        binding, current_binding = read_binding(a.current_source_binding, spec_raw)
        assert sha(a.numeric_origin.read_bytes()) == binding['original_numeric_origin_sha256']
        prepare_current_sources(binding)
    hashes, _, closures = source_closure(spec['endpoint'])
    if current_binding:
        validate_current_graph(binding, spec, hashes, closures)
        validate_contract_binding(contract, current_binding)
    else:
        assert 'current_source_binding' not in contract
        assert contract['source_endpoint_sha256'] == spec['source_endpoint_sha256']
        assert contract['source_endpoint_closure_sha256'] == spec['source_endpoint_closure_sha256']
        assert hashes[spec['endpoint']] == spec['source_endpoint_sha256']
        assert closures[spec['endpoint']] == spec['source_endpoint_closure_sha256']
    repository = os.environ['GITHUB_REPOSITORY']
    publishing_commit = os.environ['GITHUB_SHA']
    run, commit = int(os.environ['GITHUB_RUN_ID']), publishing_commit
    api = GitHub(repository)
    replacements, replacement_digest = {}, None
    original_observations = {}
    assert a.numeric_origin or not a.numeric_replacements
    if a.numeric_origin:
        origin = json.loads(a.numeric_origin.read_bytes())
        assert origin['kind'] == 'PINNED_ORIGINAL_NUMERIC_RUN_FOR_FINAL_ONLY_CONTINUATION'
        assert origin['repository'] == repository
        assert origin['numeric_spec_sha256'] == sha(a.spec.read_bytes())
        assert origin['source_endpoint_sha256'] == spec['source_endpoint_sha256']
        assert origin['source_endpoint_closure_sha256'] == spec['source_endpoint_closure_sha256']
        assert origin['numeric_jobs'] == len(spec['jobs'])
        assert isinstance(origin['run'], int) and origin['run'] > 0
        assert re.fullmatch(r'[0-9a-f]{40}', origin['source_commit'])
        run, commit = origin['run'], origin['source_commit']
        actual = api.get('/actions/runs/' + str(run))
        assert actual['id'] == run and actual['head_sha'] == commit
        assert actual['path'] == origin['workflow_path']
        assert actual['head_branch'] == origin['branch'] == 'rg-degree-one-large-20261103'
        # Recovery contracts are sealed only after concrete successful evidence
        # exists; an unresolved same-push placeholder cannot enter a continuation.
        assert contract['kind'] == 'SEALED_D1_COMPLETION_PREREQUISITES'
        for item in contract['jobs']:
            assert 'workflow_path' not in item and isinstance(item['run'], int)
            assert isinstance(item['job'], int) and item['job'] > 0
            assert re.fullmatch(r'[0-9a-f]{40}', item['source_commit'])
            assert isinstance(item['artifact_id'], int) and item['artifact_id'] > 0
            assert re.fullmatch(r'[0-9a-f]{64}', item['artifact_sha256'])
        replacements, replacement_digest = sealed_numeric_replacements(
            a.numeric_replacements, spec_raw, origin, repository)
        assert set(replacements) <= {b['batch'] for b in spec['jobs']}
        if a.numeric_replacements:
            replacement_raw = a.numeric_replacements.read_bytes()
            assert sha(replacement_raw) == replacement_digest
            annotation = json.loads(replacement_raw).get('coverage_at_sealing')
            if annotation is not None:
                from rg_numeric_alternative_coverage import REGISTRY, validate
                original_observations = validate(annotation, spec_raw,
                    (ROOT / REGISTRY).read_bytes(), replacements)
                assert actual['status'] == 'completed' and actual['run_attempt'] == 1
        if current_binding:
            assert replacements['00_137']['completion_kind'] in NUMERIC137_COMPLETIONS
            assert replacements['00_166']['completion_kind'] == NUMERIC166_JOIN

    catalogs, job_catalogs, observed_jobs = {}, {}, {}
    def jobs_for(r):
        if r not in job_catalogs:
            job_catalogs[r] = api.listing('/actions/runs/' + str(r) + '/jobs?filter=all', 'jobs')
            observed_jobs.update({j['id']: j for j in job_catalogs[r]})
        return job_catalogs[r]
    items = []
    for batch in spec['jobs']:
        plan = bound_file(batch['plan'], batch['plan_sha256'])
        if batch['batch'] in replacements:
            item = dict(replacements[batch['batch']])
            assert item['original_plan_sha256'] == batch['plan_sha256']
            if item.get('provenance_kind') == REFERENCE_COMPLETION:
                observed = observe_reference_original_job(item, spec_raw, origin, jobs_for(run))
                item['numeric_reference_completion'] = dict(kind=REFERENCE_COMPLETION,
                    sealed_replacement_sha256=replacement_digest,
                    original_batch=batch['batch'], original_plan_sha256=batch['plan_sha256'],
                    original_job_observation_at_seal=item['original_job_observation'],
                    original_job_observation_at_collection=observed)
            elif item.get('provenance_kind') == THREE_WAVE_TWO_COMPLETION:
                from rg_actual_numeric_completions import observe_three_original_job
                observed = observe_three_original_job(item, spec_raw, origin, jobs_for(run), ROOT)
                item['numeric_three_wave_two_completion'] = dict(kind=THREE_WAVE_TWO_COMPLETION,
                    sealed_replacement_sha256=replacement_digest,
                    original_batch=batch['batch'], original_plan_sha256=batch['plan_sha256'],
                    original_job_observation_at_seal=item['original_job_observation'],
                    original_job_observation_at_collection=observed)
            else:
                if 'original_job_lookup' in item:
                    old = resolve_original_job(item, spec_raw, origin, jobs_for(run))
                    del item['original_job_lookup']
                    item['original_job'] = old['id']
                else:
                    old = api.get('/actions/jobs/' + str(item['original_job']))
                assert old['run_id'] == run and old['head_sha'] == commit
                assert old['name'] == 'original-numeric-' + batch['batch']
                assert old['status'] == 'completed' and old['conclusion'] in ('failure', 'timed_out')
                item['numeric_replacement'] = dict(
                    sealed_replacement_sha256=replacement_digest, original_run=run,
                    original_job=old['id'], original_source_commit=commit,
                    original_batch=batch['batch'], original_plan_sha256=batch['plan_sha256'])
            recovered = api.get('/actions/runs/' + str(item['run']))
            assert recovered['id'] == item['run'] and recovered['head_sha'] == item['source_commit']
            assert recovered['path'] == item['workflow_path']
            assert recovered['head_branch'] == 'rg-degree-one-large-20261103'
            if item.get('provenance_kind') in {REFERENCE_COMPLETION, THREE_WAVE_TWO_COMPLETION}:
                assert type(recovered['run_attempt']) is int and recovered['run_attempt'] == 1
                assert recovered['repository']['full_name'] == repository == 'RhudeJJJJ/formal-conjectures'
            del item['workflow_path']
        else:
            job = latest_named_job(jobs_for(run), 'original-numeric-' + batch['batch'])
            if original_observations:
                from rg_numeric_alternative_coverage import require_observed_original_success
                require_observed_original_success(original_observations[batch['batch']], job)
            item = dict(run=run, job=job['id'], source_commit=commit,
                artifact_name=f"rg-d1-original-numeric-{run}-{job['run_attempt']}-{batch['batch']}",
                required_success_step='Require exact historical output identities')
        # All original endpoints remain mandatory. The fixed completion kinds
        # may bind preserved partial origins or the explicit declaration split,
        # including its separate zero-fresh audit; none may override this plan.
        item.update(key='batch' + batch['batch'], original_manifests=plan['original_manifests'],
                    fresh_module_origins=plan['fresh_module_origins'])
        items.append(item)
    for original in contract['jobs']:
        item = dict(original)
        if 'workflow_path' in item:
            assert item['source_commit'] == 'CURRENT_PUBLISHING_COMMIT'
            item['source_commit'] = publishing_commit
            workflow = pathlib.PurePosixPath(item['workflow_path'])
            assert workflow.parent == pathlib.PurePosixPath('.github/workflows') and workflow.suffix == '.yml'
            runs = api.listing('/actions/workflows/' + urllib.parse.quote(workflow.name, safe='') + '/runs?head_sha=' + publishing_commit, 'workflow_runs')
            matches = [r for r in runs if r['head_sha'] == publishing_commit and r['path'] == str(workflow)
                       and r['head_branch'] == 'rg-degree-one-large-20261103']
            assert len(matches) == 1, ('Missing or ambiguous same-commit auxiliary run', str(workflow))
            item['run'] = matches[0]['id']
        assert isinstance(item['run'], int) and re.fullmatch(r'[0-9a-f]{40}', item['source_commit'])
        if 'job' not in item:
            job = latest_named_job(jobs_for(item['run']), item['job_name'])
            item['job'] = job['id']
        else:
            job = api.get('/actions/jobs/' + str(item['job']))
            observed_jobs[job['id']] = job
        if 'artifact_name_template' in item:
            item['artifact_name'] = item['artifact_name_template'].format(run=item['run'], attempt=job['run_attempt'])
        items.append(item)
    assert len({i['key'] for i in items}) == len(items)
    deadline = time.monotonic() + a.external_wait_seconds
    for item in items:
        while True:
            job = observed_jobs.pop(item['job'], None)
            if job is None: job = api.get('/actions/jobs/' + str(item['job']))
            assert job['run_id'] == item['run'] and job['head_sha'] == item['source_commit']
            if 'job_name' in item: assert job['name'] == item['job_name']
            if item.get('provenance_kind') in {REFERENCE_COMPLETION, THREE_WAVE_TWO_COMPLETION}:
                assert job['id'] == item['job']
                assert type(job['run_attempt']) is int and job['run_attempt'] == 1
                assert job['head_branch'] == 'rg-degree-one-large-20261103'
            if job['status'] == 'completed':
                assert job['conclusion'] == 'success', ('Named prerequisite failed', item['key'], item['job'], job['conclusion'])
                item['actual_run_attempt'] = job['run_attempt']
                break
            assert item['run'] != run and time.monotonic() < deadline, ('Bounded prerequisite wait expired', item['key'])
            print(json.dumps({'status': 'WAITING_FOR_NAMED_PREREQUISITE', 'key': item['key'], 'job': item['job']}), flush=True)
            time.sleep(min(30, max(0, deadline - time.monotonic())))
        steps = [s for s in job['steps'] if s['name'] == item['required_success_step']]
        assert len(steps) == 1 and steps[0]['conclusion'] == 'success', item['key']
        if item.get('provenance_kind') in {REFERENCE_COMPLETION, THREE_WAVE_TWO_COMPLETION}:
            assert steps[0]['status'] == 'completed'
    for r in sorted({i['run'] for i in items}):
        catalogs[r] = api.listing('/actions/runs/' + str(r) + '/artifacts', 'artifacts')
    out = a.output.resolve()
    assert out.is_relative_to(ROOT / 'ci')
    out.mkdir(parents=True, exist_ok=True)
    covered, reports, current_numeric_support = {}, [], set()
    for item in items:
        expected = original_rows(item)
        completion = None
        ge46_audit = None
        if item.get('expected_kind') == 'GE46_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT':
            from rg_ge46_zero_fresh_completion import completion_context as ge46_context
            ge46_audit = ge46_context(item)
            assert 'completion_kind' not in item
        if 'completion_kind' in item:
            from rg_exact_numeric_completion import (completion_context,
                compare_completion_records, authenticate_completion)
            completion = completion_context(item)
            assert completion['original'] == expected
            if completion['kind'] == 'ORIGINAL_PARTIAL_PRIORS_WITH_FRESH_REMAINDER':
                assert item['artifact_name'] == (
                    f"rg-d1-original-numeric-remainder-20261103-{item['run']}-{item['actual_run_attempt']}-{item['batch']}")
            elif completion['kind'] == NUMERIC137_ZERO_AUDIT:
                assert item['artifact_name'] == completion['audit']['audit_archive_name_template'].format(
                    run=item['run'], attempt=item['actual_run_attempt'])
            elif completion['kind'] == NUMERIC166_JOIN:
                assert item['artifact_name'] == (
                    f"rg-d1-numeric166-complete-{item['run']}-{item['actual_run_attempt']}")
            else:
                assert item['artifact_name'] == (
                    f"rg-d1-numeric-decomposed-00_137-{item['run']}-{item['actual_run_attempt']}")
        if item.get('expected_kind') == 'existing_compact_small_ge_four_scope':
            assert hashes[item['endpoint']] == item['audit_source']['source_sha256']
            assert closures[item['endpoint']] == item['audit_source']['source_closure_sha256']
        artifacts = [x for x in catalogs[item['run']] if x['name'] == item['artifact_name']]
        assert len(artifacts) == 1, ('Missing or ambiguous original archive', item['key'])
        artifact = artifacts[0]
        assert not artifact['expired'] and artifact['workflow_run']['id'] == item['run']
        assert artifact['workflow_run']['head_sha'] == item['source_commit']
        if item.get('provenance_kind') in {REFERENCE_COMPLETION, THREE_WAVE_TWO_COMPLETION}:
            assert artifact['workflow_run']['head_branch'] == 'rg-degree-one-large-20261103'
        assert re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest'])
        if 'artifact_id' in item: assert artifact['id'] == item['artifact_id']
        if 'artifact_sha256' in item: assert artifact['digest'] == 'sha256:' + item['artifact_sha256']
        raw = api.logs(item['job'])
        fresh = records_from_log(raw)
        # Compare the complete job first. Shared ancestors are retained only
        # after identical source, closure, object, member and axiom checks.
        preserved, completion_report, endpoint_audit_report = {}, None, None
        if ge46_audit:
            from rg_ge46_zero_fresh_completion import authenticate_completion as authenticate_ge46_audit
            preserved, endpoint_audit_report = authenticate_ge46_audit(
                item, artifact, ge46_audit, fresh, hashes, closures, api)
            assert not fresh and preserved == expected
            # These are the exact old FRESH records, still attached solely to
            # the failed original proof archive. The successful audit exports
            # no objects and receives its own empty manifest below.
            proof_path = ge46_audit['audit']['proof_manifest']['path']
            proof_raw = (ROOT / proof_path).read_bytes()
            assert sha(proof_raw) == ge46_audit['audit']['proof_manifest']['sha256']
            (out / (item['key'] + '_original_kernel_prior_exports.json')).write_bytes(proof_raw)
        elif completion:
            compare_completion_records(completion, fresh, hashes, closures)
            preserved, completion_report = authenticate_completion(
                item, artifact, completion, fresh, hashes, closures, repository, api)
            assert not set(preserved).intersection(fresh)
            assert set(expected) <= set(preserved) | set(fresh)
            current_numeric_support.update((set(preserved) | set(fresh)) - set(expected))
            if completion['kind'] == NUMERIC137_ZERO_AUDIT:
                assert not fresh and preserved == completion['proof']['modules']
                proof_path = completion['audit']['proof_manifest']['path']
                proof_raw = (ROOT / proof_path).read_bytes()
                assert sha(proof_raw) == completion['audit']['proof_manifest']['sha256']
                (out / (item['key'] + '_original_kernel_prior_exports.json')).write_bytes(proof_raw)
            if completion['kind'] == NUMERIC166_JOIN:
                assert not fresh
                # The successful join compiles nothing. Preserve each leaf's
                # actual kernel origin and the old six endpoint objects.
                for leaf_key, proof in completion['authenticated_leaf_manifests'].items():
                    (out / (item['key'] + '_leaf' + leaf_key + '_original_kernel_prior_exports.json')).write_text(
                        json.dumps(proof, indent=2) + '\n')
                partial = completion['partial']
                (out / (item['key'] + '_partial_original_kernel_prior_exports.json')).write_text(
                    json.dumps(partial, indent=2) + '\n')
        else:
            compare_records(fresh, expected, hashes, closures, item.get('expected_kind') == 'new_compact_wrappers')
        for n, row in (preserved | fresh).items():
            if n in covered: assert identity(n, covered[n]) == identity(n, row), ('Conflicting cross-job identities', n)
            else: covered[n] = row
        manifest = dict(repository=repository, run=item['run'], job=item['job'],
            source_commit=item['source_commit'], artifact_id=artifact['id'],
            artifact_sha256=artifact['digest'].removeprefix('sha256:'),
            lean_version='4.33.1', mathlib=PIN, modules=fresh,
            origin_context=dict(kind='SOURCE_BOUND_SUCCESSFUL_KERNEL_JOB',
                successful_job_log_sha256=sha(raw), expected_contract_key=item['key'],
                archive_member_verification='MANDATORY_IN_FINAL_BOUNDED_RESTORE'))
        if 'numeric_replacement' in item:
            manifest['origin_context']['numeric_replacement'] = item['numeric_replacement']
        if 'numeric_reference_completion' in item:
            manifest['origin_context']['numeric_reference_completion'] = item['numeric_reference_completion']
        if 'numeric_three_wave_two_completion' in item:
            manifest['origin_context']['numeric_three_wave_two_completion'] = item['numeric_three_wave_two_completion']
        if completion_report:
            manifest['origin_context']['authenticated_full_batch_completion'] = completion_report
            if completion['kind'] == NUMERIC137_ZERO_AUDIT:
                manifest['origin_context']['kind'] = 'SOURCE_BOUND_SUCCESSFUL_ZERO_FRESH_METADATA_AUDIT'
            if completion['kind'] == NUMERIC166_JOIN:
                manifest['origin_context']['kind'] = 'SOURCE_BOUND_SUCCESSFUL_ZERO_FRESH_BATCH_JOIN'
        if endpoint_audit_report:
            manifest['origin_context']['kind'] = 'SOURCE_BOUND_SUCCESSFUL_ZERO_FRESH_METADATA_AUDIT'
            manifest['origin_context']['authenticated_composite_endpoint_completion'] = endpoint_audit_report
        (out / (item['key'] + '_prior_exports.json')).write_text(json.dumps(manifest, indent=2) + '\n')
        report = dict(key=item['key'], run=item['run'], job=item['job'], artifact_id=artifact['id'],
                      modules=len(fresh), status='SUCCESSFUL_EXACT_JOB_RECORDS_REQUIRE_AUTHENTICATED_ARCHIVE_RESTORE')
        if 'numeric_reference_completion' in item:
            report['numeric_reference_completion'] = item['numeric_reference_completion']
        if 'numeric_three_wave_two_completion' in item:
            report['numeric_three_wave_two_completion'] = item['numeric_three_wave_two_completion']
        if completion_report:
            report['authenticated_full_batch_completion'] = completion_report
            if completion['kind'] == NUMERIC137_ZERO_AUDIT:
                report['status'] = 'ACTUAL_FAILED_PROOF_OBJECTS_WITH_SEPARATE_SUCCESSFUL_ZERO_FRESH_AUDIT'
            if completion['kind'] == NUMERIC166_JOIN:
                report['status'] = 'FOUR_ACTUAL_KERNEL_LEAF_ORIGINS_WITH_SEPARATE_ZERO_FRESH_BATCH_JOIN'
        if endpoint_audit_report:
            report['status'] = 'ACTUAL_FAILED_PROOF_OBJECTS_WITH_SEPARATE_SUCCESSFUL_ZERO_FRESH_AUDIT'
            report['authenticated_composite_endpoint_completion'] = endpoint_audit_report
        reports.append(report)
        print(json.dumps(report), flush=True)
    assert set(spec['scheduled_numeric_modules']) <= covered.keys()
    if current_binding:
        from rg_numeric137_decomposed_recovery import NEW, NAME
        from rg_numeric166_decomposed_recovery import NEW as NEW166, ENDPOINTS as ENDPOINTS166
        assert current_numeric_support == (NEW - {NAME}) | (NEW166 - set(ENDPOINTS166))
        assert len(current_numeric_support) == 87
    else:
        assert not current_numeric_support
    required = set(contract['required_collected_modules']) | set(spec['scheduled_numeric_modules']) | current_numeric_support
    assert set(covered) == required, ('Collected prerequisite scope differs', sorted(set(covered) ^ required))
    (out / 'collection.json').write_text(json.dumps(dict(kind='EXACT_RECONSTRUCTION_MANIFEST_COLLECTION',
        modules=len(covered), reports=reports, kernel_proof='NO_NEW_KERNEL_RUN_IN_COLLECTOR',
        current_source_binding=current_binding,
        additional_current_numeric_support_modules=sorted(current_numeric_support),
        final_archive_and_source_closure_checks='MANDATORY'), indent=2) + '\n')


if __name__ == '__main__': main()
