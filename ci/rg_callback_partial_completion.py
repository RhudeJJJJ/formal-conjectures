"""Reuse exactly four real kernel exports from the failed, fixed final callback.

The callback's native failure remains a failure. Its archive proves only the
two historical heads and two changed intervals. All three family assembly
modules still require fresh strict kernel exports in the new source context.
"""
import argparse
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'Proofs/RG_Lean_20261019'))
from module_outputs import output_members
from rg_exact_numeric_completion import archived_fresh, identity, open_archive

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
RUN = 41771586873
JOB = 126382274319
WORKFLOW_HEAD = '1c4dd54321723bc7171e7dcab4fb28f01905038e'
PROOF_SOURCE = '3058176bc186394c43923c475ae4fc63424bea47'
WORKFLOW = '.github/workflows/rg-degree-one-large-exact-run-final-hook-20261103.yml'
ARTIFACT = 13298606637
ARTIFACT_SHA = '678c858661743a1ed63b41119eb56d4fee63a12fa830f1ebd1b7b06f3e83b97a'
EVIDENCE = 13298452006
EVIDENCE_SHA = 'c65a098b17e38ecc7e244495560ec48f40b046709f0bf7bfd4a15f72dfae2a7a'
MANIFEST = 'ci/rg_d1_callback41771586873_partial_prior_exports_20261104.json'
MANIFEST_SHA = '5261abd7410fbd6f10b786d60c03d7606f5143127c9d5900e39fb668218bc32b'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
HEADS = {'Proofs.RadenkovicGutmanD1Long10', 'Proofs.RadenkovicGutmanD1Long30'}
INTERVALS = {'Proofs.RadenkovicGutmanD1OriginalSharedSlice0080Complete',
             'Proofs.RadenkovicGutmanD1OriginalSharedSlice0098Complete'}
PARTIAL = HEADS | INTERVALS
FINAL = {'Proofs.RadenkovicGutmanD1OriginalSharedBothLong',
         'Proofs.RadenkovicGutmanOriginalDegreeOneLarge',
         'Proofs.RadenkovicGutmanRemainingThreeAssembly'}
ENDPOINT = 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
CONTEXT_MEMBER = 'Proofs/RG_Lean_20261019/build/final_continuation_context.json'
SUCCESS_STEPS = (
    'Require the exact callback event, reviewed checkout and sealed input hashes',
    'Collect exact successful numeric and named prerequisite exports',
    'Establish exact current closure and available original object coverage',
    'Authenticate and read back every selected original object and sidecar',
    'Reconstruct the two original long-class heads',
    'Require exact historical identities for both long-class heads',
    'Preserve the separate historical-head receipt and resource observation',
    'Recompute and enforce both intervals and the three-module final frontier',
    'Retain complete fresh outputs, axiom profiles, and diagnostics',
    'Preserve complete fresh proof exports in the standard archive layout',
    'Preserve original evidence and measured resource results separately',
)
FAILED_STEP = 'Check both affected intervals, final class, full family, and three-field assembly'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def origin():
    # source_commit is the native artifact workflow head, not its pinned checkout.
    return dict(repository=REPOSITORY, run=RUN, job=JOB, source_commit=WORKFLOW_HEAD,
                artifact_id=ARTIFACT, artifact_sha256=ARTIFACT_SHA)


def load_partial_manifest():
    raw = (ROOT / MANIFEST).read_bytes()
    assert sha(raw) == MANIFEST_SHA, 'Changed fixed callback partial manifest'
    data = json.loads(raw)
    assert data['kind'] == 'AUTHENTICATED_PARTIAL_CALLBACK_FRESH_EXPORTS'
    assert all(data[k] == v for k, v in origin().items())
    assert data['lean_version'] == '4.33.1' and data['mathlib'] == PIN
    assert set(data['modules']) == PARTIAL
    context = data['origin_context']
    assert context['proof_source_commit'] == PROOF_SOURCE
    assert context['workflow_head_commit'] == WORKFLOW_HEAD
    assert context['original_run_conclusion'] == context['original_job_conclusion'] == 'failure'
    assert context['complete_final_receipt_present'] is False
    for name, row in data['modules'].items():
        assert row['module'] == name and row['mode'] == 'FRESH_KERNEL_EXPORT'
        assert len(row['axiom_profiles']) == 3
        assert all(set(profile) <= ALLOWED for profile in row['axiom_profiles'])
        list(output_members(name, row))
    return data


def validate_current_sources(hashes, closures):
    data = load_partial_manifest()
    assert len(hashes) == 33659 and set(hashes) == set(closures)
    assert PARTIAL | FINAL <= hashes.keys()
    for name, row in data['modules'].items():
        assert hashes[name] == row['source_sha256'], ('Changed partial source', name)
        assert closures[name] == row['source_closure_sha256'], ('Changed partial closure', name)
    return data


def validate_selected_origins(plan):
    """Do not let a source-identical alternative replace any of these four origins."""
    data = validate_current_sources(plan['source_sha256'], plan['source_closure_sha256'])
    assert plan['endpoint'] == ENDPOINT and plan['required_modules'] == 33659
    assert set(plan['fresh_modules']) == set(plan['fresh_allowlist']) == FINAL
    assert plan['missing_original_modules'] == [] and plan['complete_original_object_coverage'] is True
    chosen = {}
    for group in plan['selected_archives']:
        for name, selected in group['selected_modules'].items():
            if name not in PARTIAL:
                continue
            assert name not in chosen
            assert all(group[k] == value for k, value in origin().items())
            assert selected['manifest'] == MANIFEST
            assert selected['row'] == data['modules'][name]
            assert group['manifests'][MANIFEST] == {'sha256': MANIFEST_SHA, 'capsule': False}
            chosen[name] = selected['row']
    assert set(chosen) == PARTIAL
    return dict(partial_modules=sorted(PARTIAL), preserved_origin=origin(), fresh_modules=sorted(FINAL))


def by_module(rows):
    if isinstance(rows, dict):
        assert all(name == row['module'] for name, row in rows.items())
        return rows
    assert isinstance(rows, list)
    result = {row['module']: row for row in rows}
    assert len(result) == len(rows)
    return result


def artifact_metadata(api, artifact_id, digest, expected_name, size):
    data = api.get('/actions/artifacts/' + str(artifact_id))
    assert data['id'] == artifact_id and data['name'] == expected_name
    assert not data['expired'] and data['size_in_bytes'] == size
    assert data['digest'] == 'sha256:' + digest
    assert data['workflow_run']['id'] == RUN
    assert data['workflow_run']['head_sha'] == WORKFLOW_HEAD
    return data


def named_profiles(archive, name, row):
    text = archive.read(name + '.log').decode()
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if name in HEADS:
        namespace = 'Gebendorfer.RadenkovicGutman.DegreeOneLongClass' + name[-2:]
        suffixes = ('partition_checked', 'budget_checked', 'normalized_target')
    else:
        namespace = 'Gebendorfer.RadenkovicGutman.' + name.removeprefix('Proofs.RadenkovicGutman')
        suffixes = ('cover_checked', 'slice_checked', 'actual_integral_lower')
    assert [declaration for declaration, _ in matches] == [namespace + '.' + s for s in suffixes]
    profiles = [sorted(set(a.strip() for a in body.split(',') if a.strip())) for _, body in matches]
    assert profiles == row['axiom_profiles']
    return {declaration: profile for (declaration, _), profile in zip(matches, profiles)}


def authenticate_partial(api, hashes, closures):
    """Authenticate actual failed-job evidence and all four real output files."""
    from rg_collect_exact_d1_reproductions import records_from_log
    data = validate_current_sources(hashes, closures)
    run = api.get('/actions/runs/' + str(RUN))
    assert run['id'] == RUN and run['run_attempt'] == 1 and run['path'] == WORKFLOW
    assert run['head_sha'] == WORKFLOW_HEAD and run['head_branch'] == 'main'
    assert run['event'] == 'workflow_run' and run['status'] == 'completed' and run['conclusion'] == 'failure'
    job = api.get('/actions/jobs/' + str(JOB))
    assert job['id'] == JOB and job['run_id'] == RUN and job['run_attempt'] == 1
    assert job['head_sha'] == WORKFLOW_HEAD and job['name'] == 'check'
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    steps = {s['name']: s for s in job['steps']}
    assert all(steps[name]['status'] == 'completed' and steps[name]['conclusion'] == 'success' for name in SUCCESS_STEPS)
    assert steps[FAILED_STEP]['status'] == 'completed' and steps[FAILED_STEP]['conclusion'] == 'failure'
    native_log = api.logs(JOB)
    assert records_from_log(native_log) == data['modules']
    assert b'RuntimeError: Timeout: Proofs.RadenkovicGutmanD1OriginalSharedBothLong' in native_log
    artifact_metadata(api, ARTIFACT, ARTIFACT_SHA, f'rg-degree-one-large-exact-hook-final-{RUN}-1', 8208435)
    artifact_metadata(api, EVIDENCE, EVIDENCE_SHA, f'rg-degree-one-large-exact-hook-final-evidence-{RUN}-1', 10391171)
    evidence_origin = dict(origin(), artifact_id=EVIDENCE, artifact_sha256=EVIDENCE_SHA)
    with open_archive(data) as current, open_archive(evidence_origin) as evidence:
        context_raw = evidence.read(CONTEXT_MEMBER)
        assert sha(context_raw) == data['origin_context']['callback_context_sha256']
        context = json.loads(context_raw)
        assert context['repository'] == REPOSITORY and context['callback_run'] == RUN and context['callback_run_attempt'] == 1
        assert context['workflow_head_commit'] == WORKFLOW_HEAD and context['proof_source_commit'] == PROOF_SOURCE
        assert context['workflow_event'] == 'workflow_run' and context['entrypoint'] == 'PINNED_MASTER_COMPLETION_EVENT'
        assert context['numeric_run'] == 41686621300 and context['upstream_status'] == 'completed'
        assert context['status'] == 'EXACT_CALLBACK_CONTEXT_ONLY_NO_NEW_KERNEL_PROOF'
        old_plan = json.loads(evidence.read('Proofs/RG_Lean_20261019/build/exact_degree_one_plan.json'))
        assert old_plan['required_modules'] == 33659 and old_plan['complete_original_object_coverage'] is True
        assert old_plan['missing_original_modules'] == [] and set(old_plan['fresh_modules']) == PARTIAL | FINAL
        assert set(old_plan['source_sha256']) == set(old_plan['source_closure_sha256']) == set(hashes)
        changed_sources = {n for n in hashes if hashes[n] != old_plan['source_sha256'][n]}
        changed_closures = {n for n in closures if closures[n] != old_plan['source_closure_sha256'][n]}
        assert changed_sources <= {'Proofs.RadenkovicGutmanD1OriginalSharedBothLong'}
        assert changed_closures <= FINAL
        archived_fresh(current, data['modules'])
        diagnostics = by_module(json.loads(current.read('diagnostics_records.json'))['modules'])
        assert set(diagnostics) == set(hashes) - FINAL
        assert {n for n, r in diagnostics.items() if r['mode'] == 'FRESH_KERNEL_EXPORT'} == PARTIAL
        assert all(diagnostics[n] == r for n, r in data['modules'].items())
        receipt_raw = current.read('receipt.json')
        assert receipt_raw == evidence.read('Proofs/RG_Lean_20261019/build/original_long_heads_receipt.json')
        head_receipt = json.loads(receipt_raw)
        head_rows = by_module(head_receipt['modules'])
        assert len(head_rows) == 3109 and set(head_receipt['endpoints']) == HEADS
        assert head_receipt['mathlib'] == PIN and head_receipt['leancert'] == LC
        assert 'version 4.33.1,' in head_receipt['lean']
        assert {n for n, r in head_rows.items() if r['mode'] == 'FRESH_KERNEL_EXPORT'} == HEADS
        assert all(head_rows[n] == data['modules'][n] for n in HEADS)
        compare = json.loads(current.read('original_numeric_compare.json'))
        assert compare['status'] == 'FRESH_KERNEL_NUMERIC_OUTPUTS_MATCH_ORIGINAL_IDENTITIES'
        assert set(compare['endpoints']) == HEADS and compare['fresh_modules'] == 2
        named, members, logical = {}, set(), 0
        for name, row in data['modules'].items():
            assert row['source_sha256'] == old_plan['source_sha256'][name] == hashes[name]
            assert row['source_closure_sha256'] == old_plan['source_closure_sha256'][name] == closures[name]
            named[name] = named_profiles(current, name, row)
            for relative, digest, size in output_members(name, row):
                assert relative not in members
                raw = current.read(relative)
                assert sha(raw) == digest and (size is None or len(raw) == size)
                members.add(relative)
                logical += len(raw)
        assert logical == 12963144 and len(members) == 4
        assert {n for n in current.namelist() if n.endswith(('.olean', '.olean.server', '.olean.private', '.ir'))} == members
        assert current.read('Proofs.RadenkovicGutmanD1OriginalSharedBothLong.log') == b''
        assert not any(n + '.json' in current.namelist() or n.replace('.', '/') + '.olean' in current.namelist() for n in FINAL)
        resource = json.loads(current.read('resource_observer.json'))
        assert resource['exit_code'] == 1 and resource['mathlib_and_lean_flags_unchanged'] is True
        assert min(s['available_bytes'] for s in resource['samples']) > 2048 * 1024**2
    return dict(status='FOUR_FIXED_CALLBACK_PARTIAL_EXPORTS_AUTHENTICATED',
        manifest=MANIFEST, manifest_sha256=MANIFEST_SHA, preserved_origin=origin(),
        proof_source_commit=PROOF_SOURCE, workflow_head_commit=WORKFLOW_HEAD,
        original_run_conclusion='failure', original_job_conclusion='failure',
        complete_final_receipt_present=False, actual_output_bytes_verified=logical,
        named_axiom_profiles=named, current_source_changes=sorted(changed_sources),
        current_closure_changes=sorted(changed_closures), partial_modules=sorted(PARTIAL),
        required_fresh_modules=sorted(FINAL), partial_objects_relabelled_as_fresh=False)


def validate_final_receipt(receipt, hashes, closures):
    """Require the exact four old origins in the new complete strict receipt."""
    data = validate_current_sources(hashes, closures)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [ENDPOINT]
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC and 'version 4.33.1,' in receipt['lean']
    rows = by_module(receipt['modules'])
    assert set(rows) == set(hashes)
    assert {n for n, r in rows.items() if r['mode'] == 'FRESH_KERNEL_EXPORT'} == FINAL
    for name, old in data['modules'].items():
        row = rows[name]
        assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
        assert row['origin'] == origin()
        assert identity(name, row) == identity(name, old)
    return dict(partial_modules=sorted(PARTIAL), preserved_origin=origin(),
                original_failed_job_unchanged=True, partial_objects_relabelled_as_fresh=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    from rg_plan_exact_degree_one_large import source_closure
    from rg_collect_exact_d1_reproductions import GitHub
    hashes, _, closures = source_closure(ENDPOINT)
    result = authenticate_partial(GitHub(REPOSITORY), hashes, closures)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
