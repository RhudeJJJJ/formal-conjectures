"""Check exact original data and current source closures for remaining Fast40 cells.

Every staged cell has a new checked acceptance proof. Existing completed exports
remain source-identical; new objects are never equated with historical hashes.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Proofs/RG_Lean_20261019'
sys.path.insert(0, str(SOURCE))
from module_outputs import output_members
import rg_assert_fast40_split as common

PREFIX = common.PREFIX
NS = common.NAMESPACE
KEYS = tuple(str(i).zfill(3) for i in range(10, 19))
COMPONENTS = {
    'Parameters': ('parameters', '0 < {cell}.young ∧ (∀ i, 0 < {cell}.width i)'),
    'Arithmetic': ('arithmetic', 'NestedArithmetic.accepts (program 1 3 4 {cell}) {cell}.poly=true'),
    'Affine': ('affine', 'NestedAffine.check 3 {cell}.poly {cell}.affine {cell}.left {cell}.width=true'),
    'Positive': ('positive', 'NestedHorner.positiveCheck 3 {cell}.degrees {cell}.affine=true'),
    'Log': ('log', 'RationalLog.accepts {cell}.squareLower {cell}.payment {cell}.logarithmK {cell}.logarithmN=true'),
}
SUFFIXES = ('', 'Data', *COMPONENTS)
NEW_CELLS = {PREFIX + 'Cell' + key + suffix for key in KEYS for suffix in SUFFIXES}
JOINS = {PREFIX} | {PREFIX + 'Cells' + str(i).zfill(2) for i in range(5, 10)}


def read_source(name):
    return (SOURCE / (name.replace('.', '/') + '.lean')).read_bytes().decode()


def preserve_original_data(snapshot, historical, spec):
    assert snapshot['kind'] == 'ORIGINAL_FAST40_REMAINING_CELL_SOURCES'
    assert set(snapshot['modules']) == JOINS - {PREFIX}
    found = set()
    for original_name, original in snapshot['modules'].items():
        source = original['source']
        assert common.sha(source.encode()) == original['source_sha256'] == historical['modules'][original_name]['source_sha256']
        matches = list(re.finditer(r'(def (cell\d+) : Cell := \{.*?\}\n)'
                                  r'(theorem \2_checked : accepts 1 3 4 \2=true)'
                                  r' := by decide \+kernel\n#print axioms \2_checked\n', source, re.S))
        assert len(matches) == (1 if original_name.endswith('09') else 2)
        expected_imports = []
        for match in matches:
            block, cell, signature = match.groups()
            key = cell.removeprefix('cell')
            assert key in KEYS and key not in found
            found.add(key)
            child = PREFIX + 'Cell' + key
            expected_imports.append(child)
            seal = spec['cell_data'][key]
            assert seal['original_module'] == original_name and seal['cell'] == cell
            assert seal['data_sha256'] == common.sha(block.encode())
            assert seal['data_bytes'] == len(block.encode()) and seal['public_signature'] == signature
            data = read_source(child + 'Data')
            actual = re.search(r'(def ' + cell + r' : Cell := \{.*?\}\n)#print axioms ' + cell + r'\n', data, re.S)
            assert actual is not None and actual[1] == block, ('Changed original data block', key)
            assert data.count('def ' + cell + ' : Cell := {') == 1
            join = read_source(child)
            assert join.count(signature + ' := by\n') == 1, ('Changed public acceptance type', key)
            assert 'def ' + cell + ' ' not in join and 'by decide +kernel' not in join
            assert '#print axioms ' + cell + '_checked\n' in join
            for suffix, (qualifier, typ) in COMPONENTS.items():
                declaration = cell + '_' + qualifier + '_checked'
                text = read_source(child + suffix)
                expected = 'theorem ' + declaration + ' : ' + typ.format(cell=cell) + ' := by decide +kernel\n'
                assert text.count(expected) == 1, ('Changed acceptance component', key, suffix)
                assert '#print axioms ' + declaration + '\n' in text
        wrapper = read_source(original_name)
        actual_imports = re.findall(r'^import (Proofs\.[\w.]+)$', wrapper, re.M)
        assert actual_imports == expected_imports
        printed = re.findall(r'^#print axioms ([\w.]+)$', wrapper, re.M)
        assert printed == [NS + '.cell' + child[-3:] + '_checked' for child in expected_imports]
    assert found == set(KEYS)


def add_prior(prior, manifest):
    assert not set(prior) & set(manifest['modules']), 'Overlapping prior sources are not expected in this bounded scope'
    prior.update(manifest['modules'])


def current_cell_priors(spec, directory):
    assert directory is not None
    assert {p.name for p in directory.glob('cell*.json')} == {'cell' + key + '.json' for key in KEYS}
    prior = {}
    for key in KEYS:
        obj = json.loads((directory / ('cell' + key + '.json')).read_bytes())
        job = spec['cell_jobs'][key]
        assert obj['repository'] == 'RhudeJJJJ/formal-conjectures'
        assert obj['run'] == int(os.environ['GITHUB_RUN_ID'])
        assert obj['source_commit'] == os.environ['GITHUB_SHA']
        assert isinstance(obj['job'], int) and obj['job'] > 0
        assert isinstance(obj['artifact_id'], int) and obj['artifact_id'] > 0
        assert re.fullmatch('[0-9a-f]{64}', obj['artifact_sha256'])
        assert obj['lean_version'] == spec['lean_version'] and obj['mathlib'] == spec['mathlib']
        assert set(obj['modules']) == set(job['modules'])
        for name, row in obj['modules'].items():
            assert row['module'] == name and row['mode'] == 'FRESH_KERNEL_EXPORT'
            assert all(row[k] == job['modules'][name][k] for k in ('source_sha256', 'source_closure_sha256'))
            assert len(row['axiom_profiles']) == 1
            assert all(set(profile) <= common.ALLOWED for profile in row['axiom_profiles'])
        add_prior(prior, obj)
    assert set(prior) == NEW_CELLS
    return prior


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--spec', type=pathlib.Path, required=True)
    p.add_argument('--key', choices=(*KEYS, 'join'), required=True)
    p.add_argument('--build-directory', type=pathlib.Path, required=True)
    p.add_argument('--cell-manifests-directory', type=pathlib.Path)
    p.add_argument('--phase', choices=('before', 'after'), default='before')
    a = p.parse_args()
    spec = json.loads(a.spec.read_bytes())
    assert spec['kind'] == 'EXACT_FAST40_REMAINING_COMPONENT_RECONSTRUCTION'
    assert spec['lean_version'] == '4.33.1' and spec['mathlib'] == common.PIN and spec['leancert'] == common.LC
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib'], spec['max_parallel_cell_jobs']) == (1, 600, 2048, 2)
    assert spec['acceptance_proof_bodies_changed'] is True
    assert set(spec['cell_jobs']) == set(spec['cell_data']) == set(KEYS)
    assert set(spec['all_new_cell_modules']) == NEW_CELLS
    assert set(spec['all_new_source_modules']) == NEW_CELLS | JOINS
    assert spec['source_graph_helper'] == 'ci/rg_assert_fast40_split.py'
    assert common.sha((ROOT / spec['source_graph_helper']).read_bytes()) == spec['source_graph_helper_sha256']
    original = common.bound_file(spec['original_manifest'], spec['original_manifest_sha256'])
    snapshot = common.bound_file(spec['original_source_snapshot'], spec['original_source_snapshot_sha256'])
    assert snapshot['historical_reference_sha256'] == spec['original_manifest_sha256']
    preserve_original_data(snapshot, original, spec)
    base = common.bound_file(spec['base_manifest'], spec['base_manifest_sha256'])
    prior = dict(base['modules'])
    if a.key == 'join':
        selected = spec['join']
        assert selected['endpoint'] == PREFIX and set(selected['modules']) == JOINS
        assert selected['required_module_count'] == 155 and selected['fresh_module_count'] == 6
        partial_names = set()
        for entry in spec['partial_manifests']:
            partial = common.bound_file(entry['path'], entry['sha256'])
            assert len(partial['modules']) == entry['module_count']
            assert set(partial['modules']) == set(entry['modules'])
            assert partial['origin_context']['endpoint_complete'] is False
            assert partial['origin_context']['post_identity_gate_passed'] is False
            add_prior(prior, partial)
            partial_names.update(partial['modules'])
        assert partial_names == set(spec['preserved_partial_modules']) and len(partial_names) == 13
        collected = current_cell_priors(spec, a.cell_manifests_directory)
        assert not set(prior) & set(collected)
        prior.update(collected)
    else:
        selected = spec['cell_jobs'][a.key]
        assert selected['endpoint'] == PREFIX + 'Cell' + a.key
        assert set(selected['modules']) == {PREFIX + 'Cell' + a.key + suffix for suffix in SUFFIXES}
        assert selected['required_module_count'] == 37 and selected['fresh_module_count'] == 7
    assert selected['key'] == a.key
    hashes, closures = common.source_graph(selected['endpoint'])
    assert len(hashes) == selected['required_module_count']
    assert set(hashes) - set(prior) == set(selected['modules'])
    for name, row in selected['modules'].items():
        assert hashes[name] == row['source_sha256'] and closures[name] == row['source_closure_sha256'], name
    if a.key == 'join':
        assert hashes[PREFIX] == original['modules'][PREFIX]['source_sha256']
        for name in spec['preserved_partial_modules']:
            assert hashes[name] == prior[name]['source_sha256'] and closures[name] == prior[name]['source_closure_sha256'], name
        counts = {name: len(original['modules'][name]['axiom_profiles']) for name in JOINS}
    else:
        counts = {name: 1 for name in selected['modules']}
    assert counts == selected['axiom_profile_counts']
    frontier = json.loads((a.build_directory / 'bounded_kernel_fallback_plan.json').read_bytes())
    assert frontier['endpoint'] == selected['endpoint']
    assert frontier['required_modules'] == selected['required_module_count']
    assert frontier['max_fresh'] == selected['fresh_module_count'] and frontier['within_bound'] is True
    assert len(frontier['fresh_modules']) == len(set(frontier['fresh_modules'])) == selected['fresh_module_count']
    assert set(frontier['fresh_modules']) == set(selected['modules'])
    if a.phase == 'before':
        print(json.dumps({
            'status': 'FAST40_REMAINING_DATA_TYPE_AND_SOURCE_BOUND_NOT_A_PROOF',
            'scope_key': a.key, 'endpoint': selected['endpoint'],
            'required_modules': selected['required_module_count'], 'fresh_modules': selected['fresh_module_count'],
            'original_data_preserved_verbatim': True, 'public_acceptance_types_preserved': True,
            'acceptance_proof_bodies_changed': True, 'kernel_check_required': True,
        }), flush=True)
        return
    receipt = json.loads((a.build_directory / 'receipt.json').read_bytes())
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [selected['endpoint']]
    assert receipt['mathlib'] == common.PIN and receipt['leancert'] == common.LC and 'version 4.33.1,' in receipt['lean']
    assert set(receipt['modules']) == set(hashes)
    fresh = {n: r for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert set(fresh) == set(selected['modules'])
    output_bytes = 0
    for name, row in receipt['modules'].items():
        assert row['module'] == name
        assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name]
        assert row['axiom_profiles'] and all(set(profile) <= common.ALLOWED for profile in row['axiom_profiles'])
        if name not in fresh:
            assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            old = prior[name]
            for key in ('source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
                assert row[key] == old[key], ('Changed authenticated prior identity', name, key)
            assert sorted(output_members(name, row)) == sorted(output_members(name, old))
            continue
        assert len(row['axiom_profiles']) == counts[name]
        assert json.loads((a.build_directory / (name + '.json')).read_bytes()) == row
        for relative, digest, size in output_members(name, row):
            path = a.build_directory / relative
            assert path.resolve().is_relative_to(a.build_directory.resolve())
            assert path.is_file() and (size is None or path.stat().st_size == size)
            with path.open('rb') as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
            output_bytes += path.stat().st_size
    print(json.dumps({
        'status': 'FAST40_REMAINING_STAGED_KERNEL_EXPORTS_VERIFIED',
        'scope_key': a.key, 'endpoint': selected['endpoint'],
        'required_modules': selected['required_module_count'], 'fresh_modules': selected['fresh_module_count'],
        'original_data_preserved_verbatim': True, 'public_acceptance_types_preserved': True,
        'acceptance_proof_bodies_changed': True, 'standard_axioms_only': True,
        'verified_fresh_output_bytes': output_bytes,
        'full_degree_one_large_closure': 'PENDING_SEPARATE_FINAL_ASSEMBLY',
    }), flush=True)


if __name__ == '__main__':
    main()

