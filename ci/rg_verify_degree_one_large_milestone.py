"""Require the completed exact kernel receipt before reporting four to three."""
import hashlib, json, os, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from rg_plan_exact_degree_one_large import FRESH, PIN, LC, ALLOWED

HEADS = {'Proofs.RadenkovicGutmanD1Long10', 'Proofs.RadenkovicGutmanD1Long30'}
ENDPOINT = 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
build = SOURCES / 'build/extension'
raw = (build / 'receipt.json').read_bytes()
receipt = json.loads(raw)
plan_raw = (SOURCES / 'build/exact_degree_one_plan.json').read_bytes()
plan = json.loads(plan_raw)
assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [ENDPOINT]
assert receipt['mathlib'] == PIN and receipt['leancert'] == LC and 'version 4.33.1,' in receipt['lean']
assert plan['complete_original_object_coverage'] and not plan['missing_original_modules']
assert set(receipt['modules']) == set(plan['source_sha256'])
assert len(receipt['modules']) == plan['required_modules']
fresh = {n: r for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
assert set(fresh) == set(FRESH) | HEADS == set(plan['fresh_modules'])
for name, row in receipt['modules'].items():
    assert row['module'] == name
    assert row['source_sha256'] == plan['source_sha256'][name]
    assert row['source_closure_sha256'] == plan['source_closure_sha256'][name]
    assert row['axiom_profiles'] or name.startswith('LeanCert.')
    assert all(set(profile) <= ALLOWED for profile in row['axiom_profiles'])
    list(output_members(name, row))
for name, row in fresh.items():
    assert json.loads((build / (name + '.json')).read_bytes()) == row
    for relative, digest, size in output_members(name, row):
        p = build / relative
        assert p.resolve().is_relative_to(build.resolve())
        assert p.is_file() and (size is None or size == p.stat().st_size)
        with p.open('rb') as stream: assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
report = {
    'status': 'KERNEL_VERIFIED_DEGREE_ONE_LARGE_AND_THREE_REMAINING_ORIGINAL_FAMILIES',
    'repository': os.environ['GITHUB_REPOSITORY'], 'source_commit': os.environ['GITHUB_SHA'],
    'run': int(os.environ['GITHUB_RUN_ID']), 'run_attempt': int(os.environ['GITHUB_RUN_ATTEMPT']),
    'endpoint': ENDPOINT, 'required_modules': len(receipt['modules']),
    'source_endpoint_sha256': plan['source_sha256'][ENDPOINT],
    'source_endpoint_closure_sha256': plan['source_closure_sha256'][ENDPOINT],
    'receipt_sha256': hashlib.sha256(raw).hexdigest(),
    'authenticated_restore_plan_sha256': hashlib.sha256(plan_raw).hexdigest(),
    'new_final_modules': sorted(FRESH), 'reconstructed_historical_heads': sorted(HEADS),
    'original_degree_one_large_scope': 'Every original tree input of degree one and order at least 53; normalized integral reserve 189/5000',
    'remaining_main_family_count': 3,
    'remaining_original_main_families': ['degreeOneMiddle', 'degreeTwoThree', 'degreeFourToFortyfive'],
    'global_rg': 'THREE_EXPLICIT_ORIGINAL_FORMAL_INPUT_OBLIGATIONS_REMAIN',
    'fresh_axiom_profiles': {n: r['axiom_profiles'] for n, r in fresh.items()},
}
(SOURCES / 'build/degree_one_large_verified_milestone.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
