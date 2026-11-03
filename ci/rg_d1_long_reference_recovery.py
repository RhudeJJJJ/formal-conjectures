"""Select exact original long-class batches after restoring sealed JSON bytes.

The original run and its plans remain unchanged. This workflow supplies new
kernel evidence only after the original source, output, member and axiom gates
pass. A separate final collector must bind each actual replacement job.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess
from rg_original_d1_numeric_reproduction import load_plan

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPEC = ROOT / 'ci/rg_d1_long_reference_recovery_20261103.json'
NUMERIC = 'ci/rg_d1_required_numeric_batches_20261103.json'
NUMERIC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound(path, digest):
    relative = pathlib.PurePosixPath(path)
    assert relative.is_relative_to('ci') and '..' not in relative.parts
    raw = (ROOT / relative).read_bytes()
    assert sha(raw) == digest, ('Changed sealed reference bytes', path)
    return json.loads(raw)


def check_scope():
    spec_raw = SPEC.read_bytes()
    spec = json.loads(spec_raw)
    assert spec['kind'] == 'EXACT_ORIGINAL_LONG_NUMERIC_REFERENCE_BYTE_RECOVERY'
    assert spec['repository'] == 'RhudeJJJJ/formal-conjectures'
    assert spec['original_run'] == 41686621300
    assert spec['original_source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert spec['original_numeric_spec'] == NUMERIC
    assert spec['original_numeric_spec_sha256'] == NUMERIC_SHA
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (2, 1200, 2048)
    assert spec['maximum_parallel_jobs'] == 4
    numeric = bound(NUMERIC, NUMERIC_SHA)
    assert numeric['kind'] == 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES'
    assert len(numeric['jobs']) == 349
    audit = spec['source_reconciliation_audit']
    assert audit == {
        'path': 'ci/rg_d1_original_reference_bytes_20261103.json',
        'sha256': 'a04e5e612ce5e927a9f121a03b2786224b84736e64cee1974eaaa8c603693dc9'}
    reconciliation = bound(audit['path'], audit['sha256'])
    assert reconciliation['kind'] == 'SEALED_ORIGINAL_REFERENCE_BYTES_RECONCILIATION'
    assert reconciliation['repository'] == spec['repository']
    assert reconciliation['original_specification'] == NUMERIC
    assert reconciliation['original_specification_sha256'] == NUMERIC_SHA
    assert reconciliation['audited_commit'] == '1ec3794cd015edc12bfda7aa45389af73cc9ab3b'
    assert reconciliation['audited_ci_tree_sha'] == '31d9dc2f0c7ad0953fbb34655c4ccfcfb7670c2b'
    assert reconciliation['actual_ci_tree_truncated'] is False
    assert reconciliation['unique_plan_references_audited'] == 352
    assert reconciliation['original_batch_and_head_plans_unchanged'] == 350
    references = spec['canonical_references']
    assert len(references) == 188
    assert set(references) == set(reconciliation['canonical_references'])
    for path, digest in references.items():
        assert re.fullmatch(r'ci/(?:rg_d1_long10_final_class_scope\d{3}|rg_shared30_final_scope\d{3})_prior_exports\.json', path)
        assert re.fullmatch(r'[0-9a-f]{64}', digest)
        current = bound(path, digest)
        row = reconciliation['canonical_references'][path]
        assert row['canonical_sha256'] == digest
        assert row['classification'] == 'EXACTLY_ONE_FINAL_LF_MISSING_FROM_REPOSITORY_BYTES'
        raw = (ROOT / path).read_bytes()
        assert raw.endswith(b'\n') and len(raw) == row['canonical_bytes'] == row['audited_bytes'] + 1
        original = raw[:-1]
        assert sha(original) == row['audited_sha256']
        assert hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest() == row['audited_git_blob_sha1']
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['canonical_git_blob_sha1']
        assert json.loads(original) == current

    affected, names, used = [], set(), set()
    for row in numeric['jobs']:
        plan = bound(row['plan'], row['plan_sha256'])
        changed = set(plan['original_manifests']).intersection(references)
        if not changed:
            continue
        assert re.fullmatch(r'(?:10|30)_\d{3}', row['batch'])
        assert plan['scope'] == 'original_long_chunk'
        assert (plan['workers'], plan['module_timeout'], plan['memory_reserve_mib']) == (2, 1200, 2048)
        for path in changed:
            assert plan['original_manifests'][path] == references[path]
        # This is the unchanged original loader, including every raw manifest
        # hash, complete fresh set, output-member shape and axiom profile.
        loaded, expected = load_plan(ROOT / row['plan'])
        assert loaded == plan
        assert not names.intersection(expected), ('Repeated original numeric scope', row['batch'])
        names.update(expected)
        used.update(changed)
        affected.append(row)
    assert used == set(references)
    assert len(affected) == spec['affected_batches'] == 186
    assert sum(row['batch'].startswith('10_') for row in affected) == 50
    assert sum(row['batch'].startswith('30_') for row in affected) == 136
    assert affected == spec['jobs'], 'Recovery order and full plans must match the original master selection'
    assert {row['batch'] for row in affected} == set(reconciliation['affected_numeric_batches'])
    assert len(names) == spec['fresh_module_count'] == 2953
    assert sorted(names) == spec['fresh_modules']
    assert names <= set(numeric['scheduled_numeric_modules'])
    return spec, sha(spec_raw), names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('matrix', 'check-batch'), required=True)
    parser.add_argument('--batch')
    args = parser.parse_args()
    spec, digest, names = check_scope()
    checkout = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert checkout == os.environ['GITHUB_SHA']
    assert os.environ['GITHUB_REPOSITORY'] == spec['repository']
    assert os.environ['GITHUB_REF'] == 'refs/heads/rg-degree-one-large-20261103'
    if args.phase == 'check-batch':
        matches = [row for row in spec['jobs'] if row['batch'] == args.batch]
        assert len(matches) == 1
        print(json.dumps(dict(status='EXACT_ORIGINAL_BATCH_AND_RAW_REFERENCE_BYTES_BOUND',
            batch=args.batch, original_plan=matches[0]['plan'], original_plan_sha256=matches[0]['plan_sha256'],
            kernel_proof='NOT_ESTABLISHED_BY_REFERENCE_BINDING')), flush=True)
        return
    assert args.batch is None
    matrix = {'include': [dict(batch=row['batch'], plan=row['plan']) for row in spec['jobs']]}
    assert len(matrix['include']) == 186 <= 256
    with open(os.environ['GITHUB_OUTPUT'], 'a', encoding='utf-8') as stream:
        stream.write('matrix=' + json.dumps(matrix, separators=(',', ':')) + '\n')
    report = dict(status='EXACT_186_ORIGINAL_LONG_BATCHES_BOUND_NOT_KERNEL_PROOF',
        recovery_registry_sha256=digest, original_numeric_spec_sha256=NUMERIC_SHA,
        original_run=spec['original_run'], original_source_commit=spec['original_source_commit'],
        new_workflow_source_commit=checkout, workflow_run=int(os.environ['GITHUB_RUN_ID']),
        workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
        batches=186, fresh_modules=len(names), maximum_parallel_jobs=4,
        workers=2, module_timeout=1200, memory_reserve_mib=2048,
        source_reconciliation_audit=spec['source_reconciliation_audit'], jobs=spec['jobs'],
        old_run_status='UNCHANGED_AND_NOT_RELABELLED',
        final_replacement_contract='REQUIRES_ACTUAL_SUCCESSFUL_JOB_AND_AUTHENTICATED_EXPORTS')
    out = ROOT / 'Proofs/RG_Lean_20261019/build/long_reference_recovery_plan'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'matrix_binding.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'jobs'}), flush=True)


if __name__ == '__main__':
    main()
