"""Bind only the three unchanged original batches outside the reference run.

This source-only scheduling record creates no successful origin. Each job must
reproduce its full original scope through the existing strict kernel and exact
historical identity gates. Actual success and authenticated archives are required
before a separately reviewed final contract may use any resulting origin.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess

from rg_original_d1_numeric_reproduction import load_plan

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPEC = 'ci/rg_d1_wave_two_three_original_20261104.json'
SPEC_SHA = '361351f15d89d7b25279f277bc2875bf98ae03e8318605f792c8c2f6db81a172'
NUMERIC = 'ci/rg_d1_required_numeric_batches_20261103.json'
NUMERIC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
BATCHES = ('00_129', '10_044', '30_013')
FRESH_COUNTS = {'00_129': 2, '10_044': 16, '30_013': 16}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound(path, digest):
    relative = pathlib.PurePosixPath(path)
    assert relative.is_relative_to('ci') and '..' not in relative.parts
    raw = (ROOT / relative).read_bytes()
    assert sha(raw) == digest, ('Changed exact input', path)
    return json.loads(raw)


def check_scope():
    spec = bound(SPEC, SPEC_SHA)
    assert spec['kind'] == 'EXACT_ORIGINAL_THREE_WAVE_TWO_BATCH_REPRODUCTION'
    assert spec['repository'] == 'RhudeJJJJ/formal-conjectures'
    assert spec['audited_base_commit'] == '97d87abf774780aa34e00899b8f1d4c2b35803c2'
    assert spec['original_run'] == 41686621300
    assert spec['original_source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert spec['original_numeric_spec'] == NUMERIC
    assert spec['original_numeric_spec_sha256'] == NUMERIC_SHA
    assert tuple(spec['batch_ids']) == BATCHES
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (2, 1200, 2048)
    assert spec['maximum_parallel_jobs'] == 2 and spec['job_timeout_minutes'] == 180
    assert spec['successful_origin_registered'] is False
    for path, digest in spec['unchanged_existing_tools'].items():
        assert sha((ROOT / path).read_bytes()) == digest, ('Changed existing strict tool', path)
    numeric = bound(NUMERIC, NUMERIC_SHA)
    assert numeric['kind'] == 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES'
    assert len(numeric['jobs']) == 349
    registered = spec['disjoint_reference_registry']
    assert registered == {
        'path': 'ci/rg_d1_original_reference_bytes_20261103.json',
        'sha256': 'a04e5e612ce5e927a9f121a03b2786224b84736e64cee1974eaaa8c603693dc9'}
    reference = bound(registered['path'], registered['sha256'])
    assert len(set(reference['affected_numeric_batches'])) == 186
    assert not set(BATCHES).intersection(reference['affected_numeric_batches'])
    selected = [row for row in numeric['jobs'] if row['batch'] in BATCHES]
    assert tuple(row['batch'] for row in selected) == BATCHES
    assert selected == spec['jobs'] and all(row['wave'] == 2 for row in selected)
    names = set()
    for row in selected:
        plan = bound(row['plan'], row['plan_sha256'])
        assert (plan['workers'], plan['module_timeout'], plan['memory_reserve_mib']) == (2, 1200, 2048)
        loaded, expected = load_plan(ROOT / row['plan'])
        assert loaded == plan and len(expected) == FRESH_COUNTS[row['batch']]
        assert not names.intersection(expected), ('Repeated original fresh module', row['batch'])
        names.update(expected)
    assert len(names) == spec['fresh_module_count'] == 34
    assert sorted(names) == spec['fresh_modules']
    assert names <= set(numeric['scheduled_numeric_modules'])
    return spec, names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('matrix', 'check-batch'), required=True)
    parser.add_argument('--batch', choices=BATCHES)
    args = parser.parse_args()
    spec, names = check_scope()
    checkout = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert re.fullmatch(r'[0-9a-f]{40}', checkout) and checkout == os.environ['GITHUB_SHA']
    assert os.environ['GITHUB_REPOSITORY'] == spec['repository']
    assert os.environ['GITHUB_REF'] == 'refs/heads/rg-degree-one-large-20261103'
    if args.phase == 'check-batch':
        matches = [row for row in spec['jobs'] if row['batch'] == args.batch]
        assert len(matches) == 1
        print(json.dumps(dict(status='EXACT_ORIGINAL_WAVE_TWO_BATCH_SCOPE_BOUND_NOT_KERNEL_PROOF',
            batch=args.batch, original_plan=matches[0]['plan'],
            original_plan_sha256=matches[0]['plan_sha256'],
            expected_fresh_modules=FRESH_COUNTS[args.batch])), flush=True)
        return
    assert args.batch is None
    matrix = {'include': [dict(batch=row['batch'], plan=row['plan']) for row in spec['jobs']]}
    assert len(matrix['include']) == 3
    with open(os.environ['GITHUB_OUTPUT'], 'a', encoding='utf-8') as stream:
        stream.write('matrix=' + json.dumps(matrix, separators=(',', ':')) + '\n')
    report = dict(status='EXACT_THREE_ORIGINAL_WAVE_TWO_BATCHES_BOUND_NOT_KERNEL_PROOF',
        scope_sha256=SPEC_SHA, original_numeric_spec_sha256=NUMERIC_SHA,
        original_run=spec['original_run'], original_source_commit=spec['original_source_commit'],
        new_workflow_source_commit=checkout, workflow_run=int(os.environ['GITHUB_RUN_ID']),
        workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
        batches=3, fresh_modules=len(names), maximum_parallel_jobs=2,
        workers=2, module_timeout=1200, memory_reserve_mib=2048, jobs=spec['jobs'],
        original_run_status='UNCHANGED_AND_NOT_RELABELLED',
        successful_origin_registered=False,
        final_contract='REQUIRES_SEPARATE_ACTUAL_SUCCESSFUL_ORIGIN_AND_ARCHIVE_AUTHENTICATION')
    out = ROOT / 'Proofs/RG_Lean_20261019/build/wave_two_three_original_plan'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'matrix_binding.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'jobs'}), flush=True)


if __name__ == '__main__':
    main()
