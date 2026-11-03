"""Check an explicitly authorized fresh frontier before kernel reconstruction.

This gate verifies source identities and bounds. It does not establish a proof;
the unmodified strict extension verifier must compile every missing module.
"""
import argparse
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Proofs/RG_Lean_20261019'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
LEANCERT = '621a43d7cf21f87872392a01e874f2f1dbddc926'

parser = argparse.ArgumentParser()
parser.add_argument('--spec', type=pathlib.Path, required=True)
parser.add_argument('--build-directory', type=pathlib.Path, required=True)
parser.add_argument('--phase', choices=('before', 'after'), default='before')
args = parser.parse_args()
spec = json.loads(args.spec.read_bytes())
original_bytes = (ROOT / spec['original_manifest']).read_bytes()
assert hashlib.sha256(original_bytes).hexdigest() == spec['original_manifest_sha256']
original = json.loads(original_bytes)
report = json.loads((args.build_directory / 'bounded_kernel_fallback_plan.json').read_bytes())
assert spec['mathlib'] == MATHLIB and spec['leancert'] == LEANCERT
assert spec['endpoint'] == report['endpoint']
expected = spec['modules']
assert expected and len(expected) == spec['fresh_module_count'] == report['max_fresh']
assert len(report['fresh_modules']) == len(set(report['fresh_modules']))
assert set(report['fresh_modules']) == set(expected), 'Unexpected fresh frontier'
assert report['within_bound'] is True

sys.path.insert(0, str(SOURCE))
from module_outputs import output_members

if args.phase == 'after':
    receipt = json.loads((args.build_directory / 'receipt.json').read_bytes())
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE'
    assert receipt['endpoints'] == [spec['endpoint']]
    assert receipt['mathlib'] == MATHLIB and receipt['leancert'] == LEANCERT
    assert 'version ' + spec['lean_version'] + ',' in receipt['lean']
    assert len(receipt['modules']) == report['required_modules']
    fresh = {name: row for name, row in receipt['modules'].items() if row['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert set(fresh) == set(expected) and len(fresh) == spec['fresh_module_count']
    byte_count = 0
    for name, row in fresh.items():
        previous = original['modules'][name]
        assert row['module'] == previous['module'] == name
        for key in ('source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
            assert row[key] == previous[key], ('Changed reconstructed identity', name, key)
        assert row['axiom_profiles'] and all(set(p) <= {'propext', 'Classical.choice', 'Quot.sound'} for p in row['axiom_profiles'])
        members = tuple(sorted(output_members(name, row)))
        assert members == tuple(sorted(output_members(name, previous))), ('Changed output members', name)
        assert json.loads((args.build_directory / (name + '.json')).read_bytes()) == row
        for rel, digest, size in members:
            path = args.build_directory / rel
            assert path.is_file() and (size is None or path.stat().st_size == size)
            with path.open('rb') as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest, ('Changed reconstructed output', name, rel)
            byte_count += path.stat().st_size
    print(json.dumps({
        'status': 'EXACT_ORIGINAL_OUTPUT_IDENTITIES_REPRODUCED',
        'endpoint': spec['endpoint'], 'fresh_modules': len(fresh),
        'original_manifest_sha256': spec['original_manifest_sha256'],
        'source_closure_output_axiom_and_member_identities_match': True,
        'verified_fresh_output_bytes': byte_count,
        'full_degree_one_large_closure': 'PENDING_SEPARATE_FINAL_ASSEMBLY',
    }, separators=(',', ':')), flush=True)
    raise SystemExit(0)

from verify import without_comments

hashes, dependencies, closures = {}, {}, {}


def visit(name):
    if name in hashes:
        return
    root = SOURCE / 'ThirdParty/LeanCert' if name.startswith('LeanCert.') else SOURCE
    raw = (root / (name.replace('.', '/') + '.lean')).read_bytes()
    code = without_comments(raw.decode())
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', code, re.M), name
    hashes[name] = hashlib.sha256(raw).hexdigest()
    dependencies[name] = sorted(set(re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$', code, re.M)))
    for dependency in dependencies[name]:
        visit(dependency)


def closure(name):
    if name not in closures:
        data = [name, hashes[name], MATHLIB, LEANCERT, [(d, closure(d)) for d in dependencies[name]]]
        closures[name] = hashlib.sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()
    return closures[name]


visit(spec['endpoint'])
assert len(hashes) == report['required_modules']
for name, identity in expected.items():
    assert hashes[name] == identity['source_sha256'], ('Changed original source', name)
    assert closure(name) == identity['source_closure_sha256'], ('Changed original closure', name)
print(json.dumps({
    'status': 'EXACT_ORIGINAL_SOURCE_FRONTIER_BOUND_NOT_A_PROOF',
    'endpoint': spec['endpoint'],
    'fresh_module_count': len(expected),
    'required_modules': len(hashes),
    'source_identity_matches': len(expected),
    'kernel_reconstruction': 'REQUIRED',
    'fresh_modules': sorted(expected),
}, separators=(',', ':')), flush=True)
