"""Diagnose only the fixed BothLong timeout; never emit a production export.

The actual failed job supplies an immutable restoration plan, not a successful
proof receipt. Every projected old object is authenticated again by the unchanged
restorer. The original endpoint remains absent while an isolated instrumented
copy is compiled with the same strict flags and resource limits.
"""
import argparse
import copy
import hashlib
import io
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time
import zipfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
BUILD = SOURCES / 'build/bothlong_phase_probe'
RESTORED = SOURCES / 'build/extension'
DIAG_SOURCES = ROOT / 'ci/rg_bothlong_phase_probe_20261104'
OBJECTS = BUILD / 'objects'
SPEC = ROOT / 'ci/rg_bothlong_phase_probe_20261104_spec.json'
SPEC_SHA = '1db97952bfc986b93a511033f997c3ce041c1a71015f29dcd4bbb55f1b456a1c'
REPO = 'RhudeJJJJ/formal-conjectures'
RUN = 41800448987
JOB = 126474623047
SOURCE = '10aa67f5f16e8ad00b30ac21332791b008b69cfe'
ORIGINAL = 'Proofs.RadenkovicGutmanD1OriginalSharedBothLong'
PROBE = ORIGINAL + 'PhaseProbe'
SOURCE_SHA = '01d60858da8d95431e0240e6c7dbf2c657111fe34dbf3a3e5a115f90797edc06'
CLOSURE_SHA = '6652bff06d82bfecc1ec12127e805f41eb2e83a79f219b2145a3969fa41ccd06'
PLAN_SHA = 'cf00d37d3bd4a5b77893ceb47bcab4f09c6defae7e02afe1a656449d2b94b100'
PLAN_MEMBER = 'Proofs/RG_Lean_20261019/build/exact_degree_one_plan.json'
RUNTIME = 'ci/rg_d1_20261103_runtime_reconstructed_exports/'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
ORIGIN_KEYS = ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')
FLAGS = ['-j1', '-DElab.async=false', '-DwarningAsError=true',
         '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
         '-Dprofiler=true', '-Dprofiler.threshold=100']
ARTIFACTS = {
    'fresh': (13311274595, 'e719249592e23b01cd5a9e274c38e7d0882d89abec82d55c1937b818f4ce6e09', 4351652,
              'rg-degree-one-large-join-repair-20261104-41800448987-1'),
    'evidence': (13312610351, '3bdea6dc64fd24f862a4b8c9e9259be608b92a429a154c7f6b080cdacbfc5c81', 9888379,
                 'rg-degree-one-large-join-repair-20261104-evidence-41800448987-1'),
}
SUCCESS_STEPS = (
    'Collect exact successful numeric and named prerequisite exports',
    'Establish exact current closure and available original object coverage',
    'Authenticate and read back every selected original object and sidecar',
    'Require exactly the three remaining fresh final modules',
    'Retain complete fresh outputs, axiom profiles, and diagnostics',
    'Preserve complete fresh proof exports in the standard archive layout',
    'Preserve original evidence and measured resource results separately',
)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def original_source():
    return SOURCES / (ORIGINAL.replace('.', '/') + '.lean')


def validate_spec():
    raw = SPEC.read_bytes()
    assert sha(raw) == SPEC_SHA
    spec = json.loads(raw)
    assert spec['source_commit'] == SOURCE and spec['original_source_sha256'] == SOURCE_SHA
    assert spec['required_compiler_flags'] == FLAGS
    assert spec['unchanged_limits'] == dict(memory_reserve_mib=2048, module_timeout_seconds=900, workers=1)
    assert spec['diagnostic_endpoint'] == PROBE
    assert spec['production_receipt_or_manifest_ingestion_forbidden'] is True
    for item in spec['artifacts']:
        path = DIAG_SOURCES / item['path']
        raw = path.read_bytes()
        assert path.resolve().is_relative_to(DIAG_SOURCES.resolve())
        assert len(raw) == item['bytes'] and sha(raw) == item['sha256']
    original = original_source().read_bytes()
    assert sha(original) == SOURCE_SHA
    probe = (DIAG_SOURCES / (PROBE.replace('.', '/') + '.lean')).read_bytes()
    stripped = b''.join(line for line in probe.splitlines(keepends=True)
        if line != b'import Proofs.RGDiagnosticPhaseMarker\n'
        and not line.startswith((b'rg_phase ', b'rg_phase_checked ')))
    assert stripped == original, 'Instrumentation changed original declarations'
    return spec


def safe_archive(raw, kind):
    _, digest, size, _ = ARTIFACTS[kind]
    assert len(raw) == size and sha(raw) == digest
    archive = zipfile.ZipFile(io.BytesIO(raw))
    names = archive.namelist()
    assert len(names) == len(set(names)) and len(names) <= 4096
    for name in names:
        path = pathlib.PurePosixPath(name)
        assert not path.is_absolute() and '..' not in path.parts
    return archive


def authenticate_failure(run, job, artifacts, log, fresh_raw, evidence_raw):
    """Pure verification of the actual failure, both complete ZIPs and old rows."""
    assert run['id'] == RUN and run['run_attempt'] == 1
    assert run['head_sha'] == SOURCE and run['head_branch'] == 'rg-degree-one-large-20261103'
    assert run['path'] == '.github/workflows/rg-degree-one-large-join-repair-20261104.yml'
    assert run['event'] == 'push' and run['status'] == 'completed' and run['conclusion'] == 'failure'
    assert job['id'] == JOB and job['run_id'] == RUN and job['run_attempt'] == 1
    assert job['head_sha'] == SOURCE and job['name'] == 'check'
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    steps = {s['name']: s for s in job['steps']}
    assert all(steps[n]['status'] == 'completed' and steps[n]['conclusion'] == 'success' for n in SUCCESS_STEPS)
    assert steps['Check final class, full family, and three-field assembly']['conclusion'] == 'failure'
    assert steps['Require the exact completed kernel milestone and remaining three scopes']['conclusion'] == 'skipped'
    from rg_collect_exact_d1_reproductions import records_from_log
    assert records_from_log(log) == {}
    assert b'RuntimeError: Timeout: Proofs.RadenkovicGutmanD1OriginalSharedBothLong' in log
    assert b'-DElab.async=false' in log and b'-Dprofiler.threshold=100' in log
    catalog = {m['id']: m for m in artifacts}
    assert len(catalog) == len(artifacts) == 2
    for artifact, digest, size, name in ARTIFACTS.values():
        meta = catalog[artifact]
        assert meta['name'] == name and not meta['expired']
        assert meta['size_in_bytes'] == size and meta['digest'] == 'sha256:' + digest
        assert meta['workflow_run']['id'] == RUN and meta['workflow_run']['head_sha'] == SOURCE
    with safe_archive(fresh_raw, 'fresh') as fresh, safe_archive(evidence_raw, 'evidence') as evidence:
        assert set(fresh.namelist()) == {ORIGINAL + '.log', 'diagnostics_records.json',
                                       'numeric137_decomposed_source.json', 'resource_observer.json'}
        assert fresh.read(ORIGINAL + '.log') == b''
        assert not any(n.endswith(('receipt.json', 'degree_one_large_verified_milestone.json')) for n in evidence.namelist())
        raw = evidence.read(PLAN_MEMBER)
        assert sha(raw) == PLAN_SHA
        plan = json.loads(raw)
        assert plan['kind'] == 'EXACT_SOURCE_BOUND_COMPRESSED_RESTORE_PLAN'
        assert plan['required_modules'] == len(plan['source_sha256']) == 33659
        assert plan['mathlib'] == PIN and plan['leancert'] == LC and plan['lean_version'] == '4.33.1'
        from rg_callback_partial_completion import FINAL, validate_selected_origins
        validate_selected_origins(plan)
        frontier = json.loads(evidence.read('Proofs/RG_Lean_20261019/build/extension/bounded_kernel_fallback_plan.json'))
        assert frontier['required_modules'] == 33659 and frontier['verified_prior_objects'] == 33656
        assert set(frontier['fresh_modules']) == FINAL and frontier['max_fresh'] == 3 and frontier['within_bound'] is True
        rows = json.loads(fresh.read('diagnostics_records.json'))['modules']
        assert isinstance(rows, list)
        diagnostics = {r['module']: r for r in rows}
        assert len(diagnostics) == len(rows) == 33656
        selected = {}
        for group in plan['selected_archives']:
            report = json.loads(evidence.read('rg-proofstore-roundtrip-reports/' + str(group['artifact_id']) + '.json'))
            assert report['status'] == 'EXACT_ORIGINAL_MEMBERS_RESTORED_AND_READ_BACK_THROUGH_COMPRESSION'
            assert report['artifact_id'] == group['artifact_id'] and report['artifact_sha256'] == group['artifact_sha256']
            assert report['modules'] == len(group['selected_modules'])
            assert report['all_declared_sidecars_preserved'] is True and report['fresh_kernel_compilations'] == 0
            for name, choice in group['selected_modules'].items():
                assert name not in selected
                row = choice['row']
                assert row['source_sha256'] == plan['source_sha256'][name]
                assert row['source_closure_sha256'] == plan['source_closure_sha256'][name]
                capsule = group['manifests'][choice['manifest']]['capsule']
                if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
                    assert capsule
                    origin = row['origin']
                else:
                    assert row['mode'] == 'FRESH_KERNEL_EXPORT'
                    origin = {k: group[k] for k in ORIGIN_KEYS}
                restored = dict(row, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=origin)
                if capsule:
                    restored['transport_capsule'] = {k: group[k] for k in ORIGIN_KEYS if k != 'repository'}
                assert diagnostics[name] == restored, ('Changed actual prior row', name)
                selected[name] = choice
        assert set(selected) == set(diagnostics) == set(plan['source_sha256']) - FINAL
        resource = json.loads(fresh.read('resource_observer.json'))
        assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == 1
        assert resource['mathlib_and_lean_flags_unchanged'] is True
        assert min(s['available_bytes'] for s in resource['samples']) > 2048 * 1024**2
        maximum = resource['maximum_aggregate_lean_rss']
        assert type(maximum) is int and maximum >= max(s['aggregate_lean_rss'] for s in resource['samples'])
        host = json.loads(evidence.read('rg-proofstore-kernel-reserve.json'))
        assert host['status'] == 'OWNED_KERNEL_GROUP_ENDED' and host['exit_code'] == 1
        assert host['host_reserve_stop'] is False and host['foreign_processes_signalled'] == 0
        runtime = {name: evidence.read(name) for name in evidence.namelist()
                   if name.startswith(RUNTIME) and name.endswith('.json')}
    report = dict(status='FIXED_FAILED_RUN_PLAN_AUTHENTICATED_NO_NEW_KERNEL_EXPORT',
        repository=REPO, run=RUN, job=JOB, source_commit=SOURCE,
        run_conclusion='failure', job_conclusion='failure', completed_fresh_modules=0,
        actual_prior_records=len(diagnostics), full_required_modules=33659,
        fixed_full_plan_sha256=PLAN_SHA,
        archives={k: dict(artifact_id=v[0], sha256=v[1], bytes=v[2]) for k, v in ARTIFACTS.items()},
        prior_object_origin_relabelled=False, complete_final_receipt_present=False)
    return plan, runtime, report


def project(plan):
    """Only the transitive original endpoint; keep every chosen origin unchanged."""
    scope = set()
    def visit(name):
        if name in scope:
            return
        scope.add(name)
        for dep in plan['source_dependencies'][name]:
            visit(dep)
    visit(ORIGINAL)
    assert len(scope) == 25192
    assert plan['source_sha256'][ORIGINAL] == SOURCE_SHA
    assert plan['source_closure_sha256'][ORIGINAL] == CLOSURE_SHA
    groups, boundaries, seen = [], {}, set()
    for old in plan['selected_archives']:
        names = scope & old['selected_modules'].keys()
        if not names:
            continue
        group = copy.deepcopy(old)
        group['selected_modules'] = {n: old['selected_modules'][n] for n in sorted(names)}
        used = {v['manifest'] for v in group['selected_modules'].values()}
        group['manifests'] = {p: old['manifests'][p] for p in sorted(used)}
        assert not seen.intersection(names)
        seen.update(names)
        if len(names) != len(old['selected_modules']):
            boundaries[old['artifact_id']] = [len(old['selected_modules']), len(names)]
        groups.append(group)
    assert len(groups) == 444 and len(seen) == 25191 and seen == scope - {ORIGINAL}
    assert boundaries == {12540313213: [141, 121], 13298606637: [4, 2]}
    result = {k: plan[k] for k in ('kind', 'mathlib', 'leancert', 'lean_version', 'kernel_proof', 'global_rg')}
    result.update(endpoint=ORIGINAL, required_modules=len(scope),
        source_sha256={n: plan['source_sha256'][n] for n in sorted(scope)},
        source_closure_sha256={n: plan['source_closure_sha256'][n] for n in sorted(scope)},
        source_dependencies={n: plan['source_dependencies'][n] for n in sorted(scope)},
        fresh_allowlist=[ORIGINAL], fresh_modules=[ORIGINAL],
        missing_original_modules=[], complete_original_object_coverage=True,
        selected_archives=groups, unavailable_candidates=[],
        physical_capacity='REQUIRES_OBSERVED_BOUNDED_RESTORE',
        import_memory='REQUIRES_OBSERVED_DIAGNOSTIC_RUN_NOT_A_PROOF',
        diagnostic_projection=dict(full_plan_sha256=PLAN_SHA, origin_run=RUN, origin_job=JOB,
            origin_source_commit=SOURCE, original_run_conclusion='failure',
            full_groups_preserved=442, boundary_groups=boundaries,
            original_endpoint_remains_uncompiled=True))
    return result


def prepare():
    validate_spec()
    assert json.loads((BUILD / 'control_result.json').read_bytes())['status'] == 'DIAGNOSTIC_MARKER_CONTROL_PASSED'
    from rg_collect_exact_d1_reproductions import GitHub
    from rg_github_artifacts import fetch_archive
    api = GitHub(REPO)
    run = api.get('/actions/runs/' + str(RUN))
    job = api.get('/actions/jobs/' + str(JOB))
    artifacts = api.listing('/actions/runs/' + str(RUN) + '/artifacts', 'artifacts')
    log = api.logs(JOB)
    raws = {}
    for kind, (artifact, digest, _, _) in ARTIFACTS.items():
        raws[kind] = fetch_archive(dict(repository=REPO, run=RUN, source_commit=SOURCE,
                                       artifact_id=artifact, artifact_sha256=digest))
    plan, runtime, report = authenticate_failure(run, job, artifacts, log, raws['fresh'], raws['evidence'])
    projected = project(plan)
    from rg_exact_final_source_binding import prepare_current_sources, BINDING
    binding_raw = (ROOT / BINDING).read_bytes()
    assert sha(binding_raw) == '48a083f8050264c03af22483d793e75bf9f8990793e91f0a46e3e9b25f7f0bbc'
    prepare_current_sources(json.loads(binding_raw))
    from rg_plan_exact_degree_one_large import source_closure
    hashes, dependencies, closures = source_closure(ORIGINAL)
    assert hashes == projected['source_sha256'], 'Changed current BothLong source scope'
    assert dependencies == projected['source_dependencies']
    assert closures == projected['source_closure_sha256'], 'Changed current BothLong source closures'
    for group in projected['selected_archives']:
        for relative, expected in group['manifests'].items():
            path = ROOT / relative
            assert path.resolve().is_relative_to(ROOT / 'ci')
            if relative.startswith(RUNTIME):
                raw = runtime[relative]
                assert sha(raw) == expected['sha256']
                if path.exists():
                    assert path.read_bytes() == raw
                else:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(raw)
            raw = path.read_bytes()
            assert sha(raw) == expected['sha256'], relative
            manifest = json.loads(raw)
            assert all(manifest[k] == group[k] for k in (*ORIGIN_KEYS, 'mathlib', 'lean_version'))
            for name, choice in group['selected_modules'].items():
                if choice['manifest'] == relative:
                    assert manifest['modules'][name] == choice['row']
    current = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert current == os.environ['GITHUB_SHA'] and re.fullmatch(r'[0-9a-f]{40}', current)
    report.update(current_workflow_source_commit=current, current_sources_equal_fixed_projection=True,
        projected_required_modules=25192, projected_prior_modules=25191,
        projected_archive_count=444, production_endpoint=ORIGINAL,
        diagnostic_copy_endpoint=PROBE, kernel_success_claim=False)
    write_json(BUILD / 'projected_plan.json', projected)
    report['projected_plan_sha256'] = sha((BUILD / 'projected_plan.json').read_bytes())
    write_json(BUILD / 'failure_authentication.json', report)
    write_json(BUILD / 'native_run.json', run)
    write_json(BUILD / 'native_job.json', job)
    write_json(BUILD / 'native_artifacts.json', artifacts)
    (BUILD / 'native_job.log').write_bytes(log)
    print(json.dumps(report), flush=True)


def require_frontier():
    validate_spec()
    plan = json.loads((BUILD / 'projected_plan.json').read_bytes())
    auth = json.loads((BUILD / 'failure_authentication.json').read_bytes())
    assert sha((BUILD / 'projected_plan.json').read_bytes()) == auth['projected_plan_sha256']
    assert plan['endpoint'] == ORIGINAL and plan['required_modules'] == 25192
    actual = json.loads((RESTORED / 'bounded_kernel_fallback_plan.json').read_bytes())
    assert actual['status'] == 'EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS'
    assert actual['endpoint'] == ORIGINAL and actual['required_modules'] == 25192
    assert actual['verified_prior_objects'] == 25191
    assert actual['fresh_modules'] == plan['fresh_modules'] == [ORIGINAL]
    assert actual['max_fresh'] == 1 and actual['within_bound'] is True
    assert not (RESTORED / (ORIGINAL + '.json')).exists()
    assert not (RESTORED / (ORIGINAL.replace('.', '/') + '.olean')).exists()
    write_json(BUILD / 'original_endpoint_preflight.json', actual)


def host_event(phase, event, **fields):
    BUILD.mkdir(parents=True, exist_ok=True)
    with (BUILD / (phase + '_host_events.jsonl')).open('a') as stream:
        stream.write(json.dumps(dict(event=event, monotonic_ns=time.monotonic_ns(), **fields)) + '\n')
        stream.flush()
        os.fsync(stream.fileno())


def compiler_environment(phase):
    env = os.environ.copy()
    if phase == 'control':
        lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, text=True).strip()
        env['LEAN_PATH'] = str(OBJECTS)
    else:
        dependency = ROOT if (ROOT / 'Mathlib').is_dir() else ROOT / '.lake/packages/mathlib'
        assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dependency, text=True).strip() == PIN
        upstream = json.loads((SOURCES / 'ThirdParty/LeanCert/UPSTREAM.json').read_bytes())
        assert upstream['commit'] == LC
        for relative, digest in upstream['source_sha256'].items():
            assert sha((SOURCES / 'ThirdParty/LeanCert' / relative).read_bytes()) == digest
        settings = json.loads(subprocess.check_output(['lake', 'env', sys.executable, '-c',
            "import os,json;print(json.dumps({k:os.environ[k] for k in ('PATH','LEAN_PATH')}))"], cwd=ROOT, text=True))
        env.update(settings)
        paths = [str((ROOT / p).resolve()) if not pathlib.Path(p).is_absolute() else p
                 for p in settings['LEAN_PATH'].split(os.pathsep) if p]
        env['LEAN_PATH'] = os.pathsep.join([str(OBJECTS), str(RESTORED), *paths])
        lean = shutil.which('lean', path=env['PATH'])
    assert lean and pathlib.Path(lean).is_file()
    version = subprocess.check_output([lean, '--version'], env=env, cwd=ROOT, text=True).strip()
    assert 'version 4.33.1,' in version
    return lean, env, version


def compile_diagnostic(phase, name, lean, env):
    sys.path.insert(0, str(SOURCES))
    from module_outputs import remove_pending_outputs, finalize_outputs
    source = DIAG_SOURCES / (name.replace('.', '/') + '.lean')
    output = OBJECTS / (name.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    pending = output.with_suffix('.olean.pending')
    remove_pending_outputs(pending)
    assert not output.exists(), 'Diagnostic worker cannot reuse an earlier compiler result'
    log = BUILD / (name + '.log')
    command = [lean, *FLAGS, '-R', str(DIAG_SOURCES), '-o', str(pending), str(source)]
    host_event(phase, 'LEAN_LAUNCH_REQUESTED', module=name, timeout_seconds=900, command=command)
    started, timeout = time.monotonic(), False
    with log.open('w') as stream:
        child = subprocess.Popen(command, cwd=DIAG_SOURCES, env=env, stdout=stream, stderr=subprocess.STDOUT)
        host_event(phase, 'LEAN_PROCESS_STARTED', module=name, pid=child.pid)
        try:
            code = child.wait(timeout=900)
        except subprocess.TimeoutExpired:
            timeout = True
            child.kill()
            code = child.wait()
    host_event(phase, 'LEAN_TIMEOUT' if timeout else 'LEAN_PROCESS_EXITED', module=name,
               pid=child.pid, returncode=code, seconds=round(time.monotonic() - started, 3))
    text = log.read_text()
    success = not timeout and code == 0 and not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', text)
    if success:
        assert pending.is_file()
        finalize_outputs(pending, output)
    else:
        remove_pending_outputs(pending)
    return dict(module=name, success=success, timeout=timeout, compiler_returncode=code,
        seconds=round(time.monotonic() - started, 3), log_sha256=sha(log.read_bytes()),
        diagnostic_output_sha256=sha(output.read_bytes()) if success else None)


def phase_labels(path, expected):
    labels, stamps = [], []
    for line in path.read_text().splitlines():
        fields = line.split('\t')
        assert len(fields) == 3 and fields[0] == 'RG_PHASE' and fields[1].isdigit()
        stamps.append(int(fields[1]))
        labels.append(fields[2])
    assert labels == expected[:len(labels)] and len(labels) <= len(expected), 'Changed marker order'
    assert stamps == sorted(stamps)
    return labels


def named_axioms(text):
    matches = re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", text, re.S)
    result = []
    for match in matches:
        axioms = sorted(set(x.strip() for x in (match[2] or '').split(',') if x.strip()))
        assert set(axioms) <= ALLOWED
        result.append(dict(declaration=match[1], axioms=axioms))
    return result


def worker(phase):
    spec = validate_spec()
    BUILD.mkdir(parents=True, exist_ok=True)
    phase_file = BUILD / (phase + '_phases.tsv')
    assert not phase_file.exists(), 'Each diagnostic phase must start with a new marker file'
    phase_file.write_text('')
    if phase == 'probe':
        require_frontier()
        control = json.loads((BUILD / 'control_result.json').read_bytes())
        assert control['status'] == 'DIAGNOSTIC_MARKER_CONTROL_PASSED'
    lean, env, version = compiler_environment(phase)
    env['RG_PHASE_LOG'] = str(phase_file.resolve())
    names = ['Proofs.RGDiagnosticPhaseMarker', 'Proofs.RGDiagnosticMarkerControl'] if phase == 'control' else [PROBE]
    results = []
    for name in names:
        result = compile_diagnostic(phase, name, lean, env)
        results.append(result)
        if not result['success']:
            break
    expected = ['control.header.complete', 'control.kernel.checked', 'control.axioms.complete'] if phase == 'control' else [m['label'] for m in spec['markers']]
    labels = phase_labels(phase_file, expected)
    success = len(results) == len(names) and all(r['success'] for r in results)
    profiles = []
    if success:
        assert labels == expected
        profiles = named_axioms((BUILD / (names[-1] + '.log')).read_text())
        expected_names = ['RGDiagnosticMarkerControl.checked'] if phase == 'control' else [
            'Gebendorfer.RadenkovicGutman.D1OriginalSharedBothLong.' + suffix for suffix in
            ('all_checked', 'adjacent_checked', 'partition_checked', 'budget_checked', 'normalized_target')]
        assert [p['declaration'] for p in profiles] == expected_names
        if phase == 'control':
            assert profiles[0]['axioms'] == []
    assert sha(original_source().read_bytes()) == SOURCE_SHA
    if phase == 'probe':
        assert not (RESTORED / (ORIGINAL + '.json')).exists()
        assert not (RESTORED / (ORIGINAL.replace('.', '/') + '.olean')).exists()
    status = 'DIAGNOSTIC_MARKER_CONTROL_PASSED' if phase == 'control' and success else 'DIAGNOSTIC_COPY_COMPILER_COMPLETED' if success else 'DIAGNOSTIC_COMPILER_FAILED_OR_TIMED_OUT'
    report = dict(status=status, phase=phase, lean=version, strict_flags=FLAGS,
        module_timeout_seconds=900, workers=1, memory_reserve_mib=2048,
        results=results, observed_phase_labels=labels, named_axiom_profiles=profiles,
        last_observed_phase=labels[-1] if labels else None,
        original_source_sha256=SOURCE_SHA, original_endpoint=ORIGINAL,
        diagnostic_endpoint=PROBE, production_receipt_created=False,
        original_kernel_export_claim=False, family_closure_claim=False,
        empty_marker_interpretation='Startup, import loading, header or first-command entry; no individual import is identified')
    write_json(BUILD / (phase + '_result.json'), report)
    print(json.dumps(report), flush=True)
    raise SystemExit(0 if success else 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('control-worker', 'prepare', 'require-frontier', 'probe-worker'), required=True)
    args = parser.parse_args()
    if args.phase == 'prepare':
        prepare()
    elif args.phase == 'require-frontier':
        require_frontier()
    else:
        worker(args.phase.removesuffix('-worker'))


if __name__ == '__main__':
    main()
