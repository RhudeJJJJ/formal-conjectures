"""Require the completed exact kernel receipt before reporting four to three."""
import hashlib, json, os, pathlib, re, subprocess, sys

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
current_binding = None
interval_rechecks = set()
if 'current_source_binding' in plan:
    from rg_exact_final_source_binding import (BINDING, NUMERIC_SPEC, NUMERIC_ORIGIN,
        binding_metadata, INTERVAL_RECHECKS)
    _, current_binding = binding_metadata((ROOT / BINDING).read_bytes(),
        (ROOT / NUMERIC_SPEC).read_bytes(), (ROOT / NUMERIC_ORIGIN).read_bytes())
    assert plan['current_source_binding'] == current_binding
    assert plan['required_modules'] == current_binding['required_modules']
    assert plan['source_sha256'][ENDPOINT] == current_binding['source_endpoint_sha256']
    assert plan['source_closure_sha256'][ENDPOINT] == current_binding['source_endpoint_closure_sha256']
    interval_rechecks = INTERVAL_RECHECKS
fresh = {n: r for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
assert set(fresh) == set(FRESH) | HEADS | interval_rechecks == set(plan['fresh_modules'])
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
proof_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
workflow_commit = os.environ['GITHUB_SHA']
assert re.fullmatch(r'[0-9a-f]{40}', proof_commit)
assert re.fullmatch(r'[0-9a-f]{40}', workflow_commit)
context = None
if os.environ.get('GITHUB_EVENT_NAME') == 'workflow_run':
    from rg_final_continuation_context import validate_context
    context = validate_context()
    assert proof_commit == context['proof_source_commit']
else:
    assert proof_commit == workflow_commit, 'Ordinary workflow checkout differs from its declared source'
report = {
    'status': 'KERNEL_VERIFIED_DEGREE_ONE_LARGE_AND_THREE_REMAINING_ORIGINAL_FAMILIES',
    'repository': os.environ['GITHUB_REPOSITORY'], 'source_commit': proof_commit,
    'proof_source_commit': proof_commit, 'workflow_head_commit': workflow_commit,
    'workflow_event': os.environ.get('GITHUB_EVENT_NAME'),
    'artifact_origin_rule': 'Reusable artifact origin uses the actual workflow head commit; proof_source_commit identifies the fixed reviewed checkout. Per-module source and closure hashes remain mandatory.',
    'run': int(os.environ['GITHUB_RUN_ID']), 'run_attempt': int(os.environ['GITHUB_RUN_ATTEMPT']),
    'endpoint': ENDPOINT, 'required_modules': len(receipt['modules']),
    'source_endpoint_sha256': plan['source_sha256'][ENDPOINT],
    'source_endpoint_closure_sha256': plan['source_closure_sha256'][ENDPOINT],
    'receipt_sha256': hashlib.sha256(raw).hexdigest(),
    'authenticated_restore_plan_sha256': hashlib.sha256(plan_raw).hexdigest(),
    'new_final_modules': sorted(FRESH), 'reconstructed_historical_heads': sorted(HEADS),
    'rechecked_current_original_intervals': sorted(interval_rechecks),
    'original_degree_one_large_scope': 'Every original tree input of degree one and order at least 53; normalized integral reserve 189/5000',
    'remaining_main_family_count': 3,
    'remaining_original_main_families': ['degreeOneMiddle', 'degreeTwoThree', 'degreeFourToFortyfive'],
    'global_rg': 'THREE_EXPLICIT_ORIGINAL_FORMAL_INPUT_OBLIGATIONS_REMAIN',
    'fresh_axiom_profiles': {n: r['axiom_profiles'] for n, r in fresh.items()},
    'current_source_binding': current_binding,
}
if context:
    report['exact_callback_context'] = context
encoded_report = json.dumps(report, indent=2) + '\n'
(SOURCES / 'build/degree_one_large_verified_milestone.json').write_text(encoded_report)
# Retain the explicit proof-source/workflow-head distinction inside the same
# authenticated archive as the fresh module records and objects.
exports = SOURCES / 'build/fresh_exports'
exports.mkdir(parents=True, exist_ok=True)
(exports / 'verified_proof_origin_and_milestone.json').write_text(encoded_report)
print(json.dumps(report), flush=True)
if os.environ.get('GITHUB_STEP_SUMMARY'):
    repository = os.environ['GITHUB_REPOSITORY']
    lines = [
        '## Verified original degreeOneLarge milestone', '',
        'The full original family and the assembly with three explicit remaining original fields passed the exact kernel and axiom audit.', '',
        f'- Fixed proof source: [{proof_commit}](https://github.com/{repository}/commit/{proof_commit})',
        f'- Actual workflow head: [{workflow_commit}](https://github.com/{repository}/commit/{workflow_commit})',
        f"- Exact receipt SHA-256: `{report['receipt_sha256']}`",
        f"- Checked local modules: {report['required_modules']}",
        '- Remaining original fields: `degreeOneMiddle`, `degreeTwoThree`, `degreeFourToFortyfive`.',
        '',
        'Three original formal input obligations remain in the global RG assembly.', '',
    ]
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a', encoding='utf-8') as stream:
        stream.write('\n'.join(lines))
