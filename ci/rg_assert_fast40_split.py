"""Bind the independent-cell split to its unchanged original declarations.

The two original cell blocks are preserved verbatim. Four exact changed/new
module identities require fresh standard-kernel exports; the five remaining
unchanged cells must also reproduce their historical object/member identities.
"""
import argparse
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Proofs/RG_Lean_20261019'
sys.path.insert(0, str(SOURCE))
from module_outputs import output_members
from verify import without_comments

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
PREFIX = 'Proofs.RadenkovicGutmanD1FastFullBox40'
NAMESPACE = 'Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40'
OLD_SOURCE = 'cba0d43c22682644cf503e3248c9350e8cd15d30eb541f561c7b4976243be607'
CHANGED = {PREFIX, PREFIX + 'Cells04', PREFIX + 'Cell008', PREFIX + 'Cell009'}
UNCHANGED = {PREFIX + 'Cells' + str(i).zfill(2) for i in range(5, 10)}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ORIGINAL_URL = ('https://github.com/RhudeJJJJ/formal-conjectures/blob/'
                '4ab5802ec7da33fcb4a54633e2e7c9863c974244/'
                'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells04.lean')


def cell_docstring(label):
    return ('\n/-!\n# Cell ' + label + ' for degree-one full box 40\n\n'
            'The cell certificate `cell' + label + '` satisfies `FastNestedCellData.accepts 1 3 4`.\n\n'
            'Source: [original cell data and acceptance theorem](' + ORIGINAL_URL + ').\n-/\n')


def wrapper_docstring():
    return ('\n/-!\n# Cells 008 and 009 for degree-one full box 40\n\n'
            'The two cell certificates satisfy `FastNestedCellData.accepts 1 3 4`.\n\n'
            'Source: [original cell data and acceptance theorems](' + ORIGINAL_URL + ').\n-/\n')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bound_file(relative, digest):
    path = pathlib.PurePosixPath(relative)
    assert path.is_relative_to('ci') and '..' not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == digest, ('Changed sealed reference', relative)
    return json.loads(raw)


def preserve_blocks(snapshot):
    assert snapshot['kind'] == 'ORIGINAL_FAST40_CELLS04_SOURCE_REFERENCE'
    assert snapshot['original_module'] == PREFIX + 'Cells04'
    assert snapshot['original_source_sha256'] == sha(snapshot['source'].encode()) == OLD_SOURCE
    pattern = (r'(?P<prefix>.*?)(?P<first>def cell008 : Cell := \{.*?#print axioms cell008_checked\n)'
               r'(?P<second>def cell009 : Cell := \{.*?#print axioms cell009_checked\n)'
               r'(?P<end>end Gebendorfer\.RadenkovicGutman\.DegreeOneFastFullBoxClass40\n)')
    match = re.fullmatch(pattern, snapshot['source'], re.S)
    assert match is not None
    assert not re.search(r'\bcell009(?:_checked)?\b', match['first'])
    assert not re.search(r'\bcell008(?:_checked)?\b', match['second'])
    for label, part in (('008', 'first'), ('009', 'second')):
        original_import = 'import Proofs.RadenkovicGutmanFastNestedCellData\n'
        assert match['prefix'].count(original_import) == 1
        prefix = match['prefix'].replace(original_import, original_import + cell_docstring(label))
        expected = (prefix + match[part] + match['end']).encode()
        path = SOURCE / ((PREFIX + 'Cell' + label).replace('.', '/') + '.lean')
        assert path.read_bytes() == expected, ('Changed original declaration/type/data/proof block', label)
    wrapper = ('/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'
               'import ' + PREFIX + 'Cell008\nimport ' + PREFIX + 'Cell009\n' + wrapper_docstring() + '\n'
               '#print axioms ' + NAMESPACE + '.cell008_checked\n'
               '#print axioms ' + NAMESPACE + '.cell009_checked\n')
    assert (SOURCE / ((PREFIX + 'Cells04').replace('.', '/') + '.lean')).read_bytes() == wrapper.encode()


def source_graph(endpoint):
    hashes, dependencies, closures = {}, {}, {}
    def visit(name):
        if name in hashes:
            return
        directory = SOURCE / 'ThirdParty/LeanCert' if name.startswith('LeanCert.') else SOURCE
        raw = (directory / (name.replace('.', '/') + '.lean')).read_bytes()
        code = without_comments(raw.decode())
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', code, re.M), name
        hashes[name] = sha(raw)
        dependencies[name] = sorted(set(re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$', code, re.M)))
        for dependency in dependencies[name]:
            visit(dependency)
    def closure(name):
        if name not in closures:
            data = [name, hashes[name], PIN, LC, [(d, closure(d)) for d in dependencies[name]]]
            closures[name] = sha(json.dumps(data, separators=(',', ':')).encode())
        return closures[name]
    visit(endpoint)
    closure(endpoint)
    return hashes, closures


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--spec', type=pathlib.Path, required=True)
    p.add_argument('--build-directory', type=pathlib.Path, required=True)
    p.add_argument('--phase', choices=('before', 'after'), default='before')
    a = p.parse_args()
    spec = json.loads(a.spec.read_bytes())
    assert spec['kind'] == 'EXACT_FAST40_INDEPENDENT_CELL_RECONSTRUCTION'
    assert spec['endpoint'] == PREFIX and spec['mathlib'] == PIN and spec['leancert'] == LC
    assert spec['lean_version'] == '4.33.1'
    assert spec['workers'] == 1 and spec['module_timeout'] == 600 and spec['memory_reserve_mib'] == 2048
    assert set(spec['split_source_exports']) == CHANGED
    assert set(spec['historical_unchanged_modules']) == UNCHANGED
    assert set(spec['modules']) == CHANGED | UNCHANGED
    assert spec['fresh_module_count'] == 9 and spec['required_module_count'] == 86
    original = bound_file(spec['original_manifest'], spec['original_manifest_sha256'])
    snapshot = bound_file(spec['original_source_snapshot'], spec['original_source_snapshot_sha256'])
    base = bound_file(spec['base_manifest'], spec['base_manifest_sha256'])
    partial = bound_file(spec['partial_manifest'], spec['partial_manifest_sha256'])
    assert set(partial['modules']) == {PREFIX + 'Cells' + str(i).zfill(2) for i in range(4)}
    assert spec['partial_module_count'] == 4
    assert not set(base['modules']) & set(partial['modules'])
    preserve_blocks(snapshot)
    hashes, closures = source_graph(spec['endpoint'])
    assert len(hashes) == 86
    expected = spec['modules']
    assert set(hashes) - set(base['modules']) - set(partial['modules']) == set(expected)
    report = json.loads((a.build_directory / 'bounded_kernel_fallback_plan.json').read_bytes())
    assert report['endpoint'] == PREFIX and report['required_modules'] == 86
    assert report['max_fresh'] == 9 and report['within_bound'] is True
    assert len(report['fresh_modules']) == len(set(report['fresh_modules'])) == 9
    assert set(report['fresh_modules']) == set(expected)
    for name, row in expected.items():
        assert hashes[name] == row['source_sha256'], ('Changed source', name)
        assert closures[name] == row['source_closure_sha256'], ('Changed source closure', name)
    assert hashes[PREFIX] == original['modules'][PREFIX]['source_sha256'], 'Fast40 head statement/source changed'
    for name in UNCHANGED:
        assert all(expected[name][k] == original['modules'][name][k] for k in ('source_sha256', 'source_closure_sha256'))
    expected_profiles = {n: original['modules'][n]['axiom_profiles'] for n in UNCHANGED | {PREFIX, PREFIX + 'Cells04'}}
    two_profiles = original['modules'][PREFIX + 'Cells04']['axiom_profiles']
    assert len(two_profiles) == 2
    for i, label in enumerate(('008', '009')):
        expected_profiles[PREFIX + 'Cell' + label] = [two_profiles[i]]
    assert spec['expected_axiom_profiles'] == expected_profiles
    if a.phase == 'before':
        print(json.dumps({'status': 'FAST40_SPLIT_SOURCE_FRONTIER_BOUND_NOT_A_PROOF',
                          'endpoint': PREFIX, 'required_modules': 86, 'fresh_modules': 9,
                          'original_source_sha256': OLD_SOURCE, 'declaration_blocks_preserved_verbatim': True,
                          'kernel_check_required': True}), flush=True)
        return
    receipt = json.loads((a.build_directory / 'receipt.json').read_bytes())
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [PREFIX]
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
    assert 'version 4.33.1,' in receipt['lean'] and len(receipt['modules']) == 86
    assert set(receipt['modules']) == set(hashes)
    fresh = {n: row for n, row in receipt['modules'].items() if row['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert set(fresh) == set(expected) and len(fresh) == 9
    byte_count = 0
    for name, row in receipt['modules'].items():
        assert row['module'] == name
        assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name]
        assert row['axiom_profiles'] and all(set(profile) <= ALLOWED for profile in row['axiom_profiles'])
        if name not in fresh:
            assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            previous = partial['modules'].get(name) or base['modules'][name]
            for key in ('source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
                assert row[key] == previous[key], ('Changed prior identity', name, key)
            assert sorted(output_members(name, row)) == sorted(output_members(name, previous))
            continue
        assert row['axiom_profiles'] == expected_profiles[name]
        if name in UNCHANGED:
            previous = original['modules'][name]
            assert row['output_sha256'] == previous['output_sha256'], ('Changed historical object', name)
            assert sorted(output_members(name, row)) == sorted(output_members(name, previous)), ('Changed historical members', name)
        # The four explicitly changed/new sources need their own fresh objects.
        # Their object hashes must not be equated with historical module hashes.
        assert json.loads((a.build_directory / (name + '.json')).read_bytes()) == row
        for relative, digest, size in output_members(name, row):
            path = a.build_directory / relative
            assert path.resolve().is_relative_to(a.build_directory.resolve()), ('Output outside build directory', name, relative)
            assert path.is_file() and (size is None or path.stat().st_size == size)
            with path.open('rb') as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest, ('Changed fresh output bytes', name, relative)
            byte_count += path.stat().st_size
    print(json.dumps({'status': 'FAST40_SPLIT_STANDARD_KERNEL_EXPORTS_VERIFIED',
                      'endpoint': PREFIX, 'required_modules': 86, 'fresh_modules': 9,
                      'unchanged_historical_objects_reproduced': 5, 'new_source_bound_exports': 4,
                      'declaration_blocks_preserved_verbatim': True, 'standard_axioms_only': True,
                      'verified_fresh_output_bytes': byte_count,
                      'full_degree_one_large_closure': 'PENDING_SEPARATE_FINAL_ASSEMBLY'}), flush=True)


if __name__ == '__main__':
    main()
