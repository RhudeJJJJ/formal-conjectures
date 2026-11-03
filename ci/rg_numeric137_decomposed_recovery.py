"""Check the complete original batch with one declaration-preserving leaf split.

The original plan and all ten endpoint names remain sealed. Nine original
modules must reproduce their historical objects. Leaf01370 keeps every original
declaration, type, data expression and proof body, divided across twelve current
modules whose objects require fresh standard-kernel checking.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from verify import without_comments
from rg_original_d1_numeric_reproduction import load_plan
from rg_plan_exact_degree_one_large import source_closure

NAME = 'Proofs.RadenkovicGutmanD1Long00Leaf01370'
ORIGINAL_SHA = '2de5bd169cbd32895022518673a22a57847f868d9ddc64f27a433519e92df1d7'
ORIGINAL_PLAN_SHA = '87a9e926ba76df68fbf0d66c6c3d32273b4db143c0c24730f3f8aa652876e74a'
MASTER_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NEW = {NAME, NAME + 'Base', NAME + 'Affine'} | {NAME + f'Rows{i:02d}' for i in range(9)}
ENDPOINTS = [f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in range(1370, 1380)]
SPEC = 'ci/rg_d1_numeric137_decomposed_20261103_spec.json'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound_file(relative, digest):
    path = pathlib.PurePosixPath(relative)
    assert path.is_relative_to('ci') and '..' not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == digest, ('Changed sealed input', relative)
    return json.loads(raw)


def context(spec_sha):
    spec = bound_file(SPEC, spec_sha)
    assert spec['kind'] == 'SOURCE_PRESERVING_NUMERIC137_FULL_BATCH_RECONSTRUCTION'
    assert spec['batch_id'] == '00_137' and spec['endpoints'] == ENDPOINTS
    assert spec['original_master_source_commit'] == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
    assert spec['mathlib'] == PIN and spec['leancert'] == LC and spec['lean_version'] == '4.33.1'
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (1, 1200, 2048)
    assert spec['original_plan_sha256'] == ORIGINAL_PLAN_SHA
    assert spec['original_master_spec_sha256'] == MASTER_SHA
    master = bound_file(spec['original_master_spec'], MASTER_SHA)
    assert len(master['scheduled_numeric_modules']) == len(set(master['scheduled_numeric_modules'])) == 4567
    bound_file(spec['original_plan'], ORIGINAL_PLAN_SHA)
    plan, expected = load_plan(ROOT / spec['original_plan'])
    assert plan['endpoints'] == ENDPOINTS and set(expected) == set(ENDPOINTS)
    assert expected[NAME]['source_sha256'] == ORIGINAL_SHA
    assert spec['base_manifest'] == plan['base_manifest']
    assert spec['base_manifest_sha256'] == plan['base_manifest_sha256']
    base = bound_file(spec['base_manifest'], spec['base_manifest_sha256'])
    snapshot = bound_file(spec['original_source_snapshot'], spec['original_source_snapshot_sha256'])
    assert spec['source_reorganized_original_modules'] == [NAME]
    assert set(spec['added_support_modules']) == NEW - {NAME}
    assert set(spec['new_source_exports']) == NEW
    assert set(spec['historical_unchanged_numeric_modules']) == set(ENDPOINTS) - {NAME}
    assert spec['proof_bodies_changed'] is False and spec['original_declarations_preserved_verbatim'] is True
    assert (spec['original_definitions'], spec['original_theorems'], spec['original_axiom_prints']) == (133, 313, 313)
    assert (spec['required_module_count'], spec['prior_module_count'], spec['fresh_module_count']) == (95, 74, 21)
    assert spec['original_numeric_module_count'] == 10
    assert len(spec['required_modules']) == len(set(spec['required_modules'])) == 95
    assert set(spec['modules']) == NEW | set(ENDPOINTS)
    assert set(spec['required_source_sha256']) == set(spec['required_source_closure_sha256']) == set(spec['required_modules'])
    assert set(spec['required_modules']) - set(base['modules']) == set(spec['modules'])
    return spec, plan, expected, base, snapshot


def preserve_declarations(spec, expected, snapshot):
    assert snapshot['kind'] == 'ORIGINAL_NUMERIC1370_DECLARATION_SOURCE_REFERENCE'
    assert snapshot['original_module'] == NAME
    assert snapshot['original_source_commit'] == spec['original_master_source_commit']
    original = snapshot['source']
    assert sha(original.encode()) == snapshot['original_source_sha256'] == ORIGINAL_SHA
    assert snapshot['header'] + snapshot['body'] + snapshot['footer'] == original
    assert snapshot['imports'] + snapshot['context'] == snapshot['header']
    assert snapshot['namespace'] == 'Gebendorfer.RadenkovicGutman.DegreeOneLongClass00'
    assert snapshot['footer'] == 'end ' + snapshot['namespace'] + '\n'
    parts = snapshot['parts']
    assert len(parts) == 12 and {p['module'] for p in parts} == NEW
    assert [p['label'] for p in parts] == ['Base', 'Affine'] + [f'Rows{i:02d}' for i in range(9)] + ['']
    old_profiles = expected[NAME]['axiom_profiles']
    assert len(old_profiles) == 313
    offset = profile_offset = 0
    declarations = []
    for part in parts:
        name = part['module']
        assert name == NAME + part['label'] and part['start'] == offset
        assert part['end'] > offset
        block = snapshot['body'][offset:part['end']]
        assert sha(block.encode()) == part['body_sha256']
        assert len(re.findall(r'^def ', block, re.M)) == part['definitions']
        assert len(re.findall(r'^theorem ', block, re.M)) == part['theorems']
        prints = re.findall(r'^#print axioms (.+)$', block, re.M)
        assert prints == part['axiom_declarations'] and prints
        declarations.extend(prints)
        offset = part['end']
        assert set(part['additional_imports']) <= NEW - {name}
        source = (snapshot['imports'] + ''.join('import ' + n + '\n' for n in part['additional_imports'])
                  + part['docstring'] + snapshot['context'] + block + snapshot['footer']).encode()
        actual = (SOURCES / (name.replace('.', '/') + '.lean')).read_bytes()
        assert actual == source, ('Changed original declaration/type/data/proof block', name)
        assert sha(actual) == spec['modules'][name]['source_sha256']
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', without_comments(actual.decode()), re.M)
        count = len(prints)
        assert spec['modules'][name]['axiom_profiles'] == old_profiles[profile_offset:profile_offset + count]
        profile_offset += count
    assert offset == len(snapshot['body']) and profile_offset == 313
    assert declarations == re.findall(r'^#print axioms (.+)$', snapshot['body'], re.M)
    assert len(declarations) == len(set(declarations)) == 313
    assert sum(p['definitions'] for p in parts) == 133
    assert sum(p['theorems'] for p in parts) == 313
    assert '#print axioms leaf01370_checked\n' in snapshot['body'][parts[-1]['start']:]


def materialize_unchanged(spec, expected, snapshot):
    """Reproduce original data in memory; never overwrite the reorganized leaf."""
    producer = bound_file(spec['producer_plan'], spec['producer_plan_sha256'])
    for relative, digest in producer['producer_source_sha256'].items():
        path = pathlib.PurePosixPath(relative)
        assert path.is_relative_to('ci') and '..' not in path.parts
        assert sha((ROOT / path).read_bytes()) == digest
    entry = producer['classes']['00']
    assert 137 in entry['open_chunk_indices']
    packet_path = pathlib.PurePosixPath(entry['packet'])
    assert not packet_path.is_absolute() and '..' not in packet_path.parts
    packet_raw = (ROOT / packet_path).read_bytes()
    assert sha(packet_raw) == entry['packet_sha256']
    packet = json.loads(packet_raw)
    from rg_shared_arm_common import module
    from rg_shared_arm_source import body
    leaves = []

    def walk(node):
        if node['kind'] in ('first', 'second'):
            walk(node['left'])
            walk(node['right'])
        else:
            assert node['kind'] == 'polynomial'
            leaves.append(node)

    for cell in packet['cells']:
        walk(cell['tree'])
    assert len(leaves) == entry['leaf_count']
    for index in range(1370, 1380):
        name = f'Proofs.RadenkovicGutmanD1Long00Leaf{index:05d}'
        imports, text = body('00', index, leaves[index], shared_weights=True)
        raw = module('DegreeOneLongClass00', imports, text).encode()
        assert sha(raw) == expected[name]['source_sha256'], ('Original producer changed', name)
        if name == NAME:
            assert raw == snapshot['source'].encode()
            continue
        target = SOURCES / (name.replace('.', '/') + '.lean')
        if target.exists():
            assert target.read_bytes() == raw, ('Unchanged original leaf differs', name)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)


def source_scope(spec, expected, base):
    hashes, closures = {}, {}
    for endpoint in ENDPOINTS:
        h, _, c = source_closure(endpoint)
        hashes.update(h)
        closures.update(c)
    assert hashes == spec['required_source_sha256']
    assert closures == spec['required_source_closure_sha256']
    for name, row in spec['modules'].items():
        assert hashes[name] == row['source_sha256'] and closures[name] == row['source_closure_sha256']
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
    for name in set(ENDPOINTS) - {NAME}:
        old = expected[name]
        for key in ('source_sha256', 'source_closure_sha256', 'axiom_profiles'):
            assert spec['modules'][name][key] == old[key], ('Unchanged original identity', name, key)
    for name in set(hashes) - set(spec['modules']):
        assert hashes[name] == base['modules'][name]['source_sha256']
        assert closures[name] == base['modules'][name]['source_closure_sha256']
    return hashes, closures


def report(name, data):
    directory = SOURCES / 'build/fresh_exports'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / ('numeric137_decomposed_' + name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec-sha256', required=True)
    parser.add_argument('--phase', choices=('materialize', 'cache', 'preflight', 'kernel', 'compare'), required=True)
    args = parser.parse_args()
    spec, plan, expected, base, snapshot = context(args.spec_sha256)
    preserve_declarations(spec, expected, snapshot)
    if args.phase == 'materialize':
        materialize_unchanged(spec, expected, snapshot)
        preserve_declarations(spec, expected, snapshot)
    hashes, closures = source_scope(spec, expected, base)
    build = SOURCES / 'build/extension'
    if args.phase == 'materialize':
        report('source', {
            'status': 'COMPLETE_ORIGINAL_BATCH_SOURCE_CONSERVATION_CHECKED_NO_KERNEL_PROOF',
            'original_endpoints': ENDPOINTS, 'required_modules': 95, 'fresh_modules': 21,
            'original_declarations_preserved_verbatim': True,
            'unchanged_original_numeric_modules': 9, 'source_reorganized_original_numeric_modules': [NAME],
            'added_support_modules': 11,
        })
    elif args.phase == 'cache':
        subprocess.run([sys.executable, '-B', 'ci/rg_run_original_d1_numeric.py',
                        '--plan', spec['original_plan'], '--phase', 'cache'], cwd=ROOT, check=True)
    elif args.phase == 'preflight':
        observed = set()
        frontiers = []
        for endpoint in ENDPOINTS:
            subprocess.run([sys.executable, '-B', 'ci/rg_restore_with_kernel_fallback.py',
                            '--plan', 'ci/rg_empty_restore_plan.json', '--build-directory', str(build),
                            '--endpoint', endpoint, '--max-fresh', '21', '--preflight-only'], cwd=ROOT, check=True)
            frontier = json.loads((build / 'bounded_kernel_fallback_plan.json').read_bytes())
            assert frontier['endpoint'] == endpoint and frontier['within_bound'] is True
            assert len(frontier['fresh_modules']) == len(set(frontier['fresh_modules']))
            assert set(frontier['fresh_modules']) <= set(spec['modules'])
            observed.update(frontier['fresh_modules'])
            frontiers.append(frontier)
        assert observed == set(spec['modules'])
        report('frontier', {
            'status': 'COMPLETE_ORIGINAL_BATCH_AND_SUPPORT_FRONTIER_BOUND_NO_KERNEL_PROOF',
            'original_endpoints': ENDPOINTS, 'required_modules': 95, 'fresh_modules': 21,
            'fresh_module_names': sorted(observed), 'frontiers': frontiers,
        })
    elif args.phase == 'kernel':
        command = [sys.executable, '-B', 'ci/rg_observed_kernel_verify.py',
                   '--memory-reserve-mib', '2048', '--', '--mathlib-project', str(ROOT)]
        for endpoint in ENDPOINTS:
            command.extend(['--endpoint', endpoint])
        command.extend(['--workers', '1', '--module-timeout', '1200', '--resume'])
        subprocess.run(command, cwd=ROOT, check=True)
    else:
        receipt = json.loads((build / 'receipt.json').read_bytes())
        assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == ENDPOINTS
        assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
        assert 'version 4.33.1,' in receipt['lean'] and set(receipt['modules']) == set(hashes)
        fresh = {n: r for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
        assert set(fresh) == set(spec['modules']) and len(fresh) == 21
        logical = 0
        for name, row in receipt['modules'].items():
            assert row['module'] == name
            assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name]
            assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
            if name not in fresh:
                assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
                old = base['modules'][name]
            else:
                assert row['axiom_profiles'] == spec['modules'][name]['axiom_profiles']
                assert row == json.loads((build / (name + '.json')).read_bytes())
                old = expected[name] if name in set(ENDPOINTS) - {NAME} else None
            if old is not None:
                for key in ('source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
                    assert row[key] == old[key], ('Changed retained historical identity', name, key)
                assert sorted(output_members(name, row)) == sorted(output_members(name, old))
            if name in fresh:
                for relative, digest, size in output_members(name, row):
                    path = build / relative
                    assert path.resolve().is_relative_to(build.resolve())
                    assert path.is_file() and (size is None or path.stat().st_size == size)
                    with path.open('rb') as stream:
                        assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
                    logical += path.stat().st_size
        report('verified', {
            'status': 'COMPLETE_ORIGINAL_BATCH_WITH_DECLARATION_PRESERVING_SPLIT_KERNEL_VERIFIED',
            'original_plan_sha256': ORIGINAL_PLAN_SHA, 'current_spec_sha256': args.spec_sha256,
            'original_endpoints': ENDPOINTS, 'required_modules': 95, 'prior_modules': 74, 'fresh_modules': 21,
            'unchanged_historical_numeric_objects_reproduced': 9,
            'source_reorganized_original_numeric_modules': [NAME], 'added_support_modules': 11,
            'original_declarations_preserved_verbatim': True, 'proof_bodies_changed': False,
            'standard_axioms_only': True, 'verified_fresh_output_bytes': logical,
            'full_degree_one_large_closure': 'PENDING_SEPARATE_FINAL_ASSEMBLY',
        })


if __name__ == '__main__':
    main()
