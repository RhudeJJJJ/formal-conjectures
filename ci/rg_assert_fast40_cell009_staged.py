"""Bind the staged Cell009 proof to original data and the exact acceptance type.

The acceptance proof body is intentionally new. Each component and the join
requires a fresh standard-kernel export. Only five unchanged cell modules are
compared with historical object hashes; Cell008 is a previously checked prior.
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
import rg_assert_fast40_split as common

PREFIX = common.PREFIX
UNCHANGED = common.UNCHANGED
COMPONENTS = {
    'Parameters': ('cell009_parameters_checked', '0 < cell009.young ∧ (∀ i, 0 < cell009.width i)'),
    'Arithmetic': ('cell009_arithmetic_checked', 'NestedArithmetic.accepts (program 1 3 4 cell009) cell009.poly=true'),
    'Affine': ('cell009_affine_checked', 'NestedAffine.check 3 cell009.poly cell009.affine cell009.left cell009.width=true'),
    'Positive': ('cell009_positive_checked', 'NestedHorner.positiveCheck 3 cell009.degrees cell009.affine=true'),
    'Log': ('cell009_log_checked', 'RationalLog.accepts cell009.squareLower cell009.payment cell009.logarithmK cell009.logarithmN=true'),
}
CHANGED = {PREFIX, PREFIX + 'Cells04', PREFIX + 'Cell009', PREFIX + 'Cell009Data'} | {
    PREFIX + 'Cell009' + suffix for suffix in COMPONENTS
}
PUBLIC_SIGNATURE = 'theorem cell009_checked : accepts 1 3 4 cell009=true'


def preserve_data_and_type(snapshot, spec):
    assert snapshot['kind'] == 'ORIGINAL_FAST40_CELLS04_SOURCE_REFERENCE'
    assert snapshot['original_source_sha256'] == common.sha(snapshot['source'].encode()) == common.OLD_SOURCE
    match = re.search(r'(def cell009 : Cell := \{.*?\}\n)(' + re.escape(PUBLIC_SIGNATURE)
                      + r') := by decide \+kernel\n', snapshot['source'], re.S)
    assert match is not None
    block = match[1]
    assert common.sha(block.encode()) == spec['original_data_block_sha256']
    data = (SOURCE / (PREFIX.replace('.', '/') + 'Cell009Data.lean')).read_text()
    assert data.count('def cell009 : Cell := {') == 1
    actual = re.search(r'(def cell009 : Cell := \{.*?\}\n)#print axioms cell009\n', data, re.S)
    assert actual is not None and actual[1] == block, 'Original cell009 data changed'
    join = (SOURCE / (PREFIX.replace('.', '/') + 'Cell009.lean')).read_text()
    assert join.count(PUBLIC_SIGNATURE + ' := by\n') == 1, 'Public acceptance theorem type changed'
    assert 'def cell009 ' not in join and 'by decide +kernel' not in join
    assert '#print axioms cell009_checked\n' in join
    for suffix, (declaration, typ) in COMPONENTS.items():
        text = (SOURCE / (PREFIX.replace('.', '/') + 'Cell009' + suffix + '.lean')).read_text()
        assert text.count('theorem ' + declaration + ' : ' + typ + ' := by decide +kernel\n') == 1
        assert '#print axioms ' + declaration + '\n' in text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', type=pathlib.Path, required=True)
    parser.add_argument('--build-directory', type=pathlib.Path, required=True)
    parser.add_argument('--phase', choices=('before', 'after'), default='before')
    args = parser.parse_args()
    spec = json.loads(args.spec.read_bytes())
    assert spec['kind'] == 'EXACT_FAST40_COMPONENT_RECONSTRUCTION'
    assert spec['endpoint'] == PREFIX and spec['mathlib'] == common.PIN and spec['leancert'] == common.LC
    assert spec['lean_version'] == '4.33.1'
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (1, 600, 2048)
    assert spec['acceptance_proof_body_changed'] is True
    assert spec['original_public_acceptance_signature'] == PUBLIC_SIGNATURE
    assert spec['preserved_completed_module'] == PREFIX + 'Cell008'
    assert set(spec['new_or_changed_source_exports']) == CHANGED
    assert set(spec['historical_unchanged_modules']) == UNCHANGED
    assert set(spec['modules']) == CHANGED | UNCHANGED
    assert spec['fresh_module_count'] == 14 and spec['required_module_count'] == 92
    helper = ROOT / 'ci/rg_assert_fast40_split.py'
    assert common.sha(helper.read_bytes()) == spec['source_graph_helper_sha256']
    original = common.bound_file(spec['original_manifest'], spec['original_manifest_sha256'])
    snapshot = common.bound_file(spec['original_source_snapshot'], spec['original_source_snapshot_sha256'])
    previous = common.bound_file(spec['previous_split_spec'], spec['previous_split_spec_sha256'])
    base = common.bound_file(spec['base_manifest'], spec['base_manifest_sha256'])
    prior = dict(base['modules'])
    partial_names = set()
    for entry in spec['partial_manifests']:
        partial = common.bound_file(entry['path'], entry['sha256'])
        assert set(partial['modules']) == set(entry['modules'])
        assert len(partial['modules']) == entry['module_count']
        assert partial['origin_context']['endpoint_complete'] is False
        assert partial['origin_context']['post_identity_gate_passed'] is False
        assert not set(prior) & set(partial['modules'])
        prior.update(partial['modules'])
        partial_names.update(partial['modules'])
    assert partial_names == {PREFIX + 'Cell008'} | {PREFIX + 'Cells' + str(i).zfill(2) for i in range(4)}
    assert spec['partial_module_count'] == len(partial_names) == 5
    preserve_data_and_type(snapshot, spec)
    hashes, closures = common.source_graph(PREFIX)
    assert len(hashes) == 92 and set(hashes) - set(prior) == set(spec['modules'])
    preserved = prior[PREFIX + 'Cell008']
    assert hashes[PREFIX + 'Cell008'] == preserved['source_sha256'] == previous['modules'][PREFIX + 'Cell008']['source_sha256']
    assert closures[PREFIX + 'Cell008'] == preserved['source_closure_sha256'] == previous['modules'][PREFIX + 'Cell008']['source_closure_sha256']
    assert hashes[PREFIX] == original['modules'][PREFIX]['source_sha256']
    assert hashes[PREFIX + 'Cells04'] == previous['modules'][PREFIX + 'Cells04']['source_sha256']
    for name, row in spec['modules'].items():
        assert hashes[name] == row['source_sha256'], ('Changed staged source', name)
        assert closures[name] == row['source_closure_sha256'], ('Changed staged closure', name)
    for name in UNCHANGED:
        assert all(spec['modules'][name][k] == original['modules'][name][k]
                   for k in ('source_sha256', 'source_closure_sha256'))
    counts = {name: (len(original['modules'][name]['axiom_profiles'])
                    if name in UNCHANGED | {PREFIX, PREFIX + 'Cells04'} else 1)
              for name in spec['modules']}
    assert counts == spec['axiom_profile_counts']
    frontier = json.loads((args.build_directory / 'bounded_kernel_fallback_plan.json').read_bytes())
    assert frontier['endpoint'] == PREFIX and frontier['required_modules'] == 92
    assert frontier['max_fresh'] == 14 and frontier['within_bound'] is True
    assert len(frontier['fresh_modules']) == len(set(frontier['fresh_modules'])) == 14
    assert set(frontier['fresh_modules']) == set(spec['modules'])
    if args.phase == 'before':
        print(json.dumps({
            'status': 'FAST40_STAGED_DATA_TYPE_AND_SOURCE_FRONTIER_BOUND_NOT_A_PROOF',
            'endpoint': PREFIX, 'required_modules': 92, 'fresh_modules': 14,
            'original_data_preserved_verbatim': True, 'public_acceptance_type_preserved': True,
            'acceptance_proof_body_changed': True, 'cell008_source_closure_preserved': True,
            'kernel_check_required': True,
        }), flush=True)
        return
    receipt = json.loads((args.build_directory / 'receipt.json').read_bytes())
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [PREFIX]
    assert receipt['mathlib'] == common.PIN and receipt['leancert'] == common.LC
    assert 'version 4.33.1,' in receipt['lean']
    assert set(receipt['modules']) == set(hashes)
    fresh = {n: r for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert set(fresh) == set(spec['modules']) and len(fresh) == 14
    byte_count = 0
    for name, row in receipt['modules'].items():
        assert row['module'] == name
        assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name]
        assert row['axiom_profiles'] and all(set(p) <= common.ALLOWED for p in row['axiom_profiles'])
        if name not in fresh:
            assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            old = prior[name]
            for key in ('source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
                assert row[key] == old[key], ('Changed authenticated prior identity', name, key)
            assert sorted(output_members(name, row)) == sorted(output_members(name, old))
            continue
        assert len(row['axiom_profiles']) == counts[name]
        if name in UNCHANGED:
            old = original['modules'][name]
            assert row['output_sha256'] == old['output_sha256']
            assert row['axiom_profiles'] == old['axiom_profiles']
            assert sorted(output_members(name, row)) == sorted(output_members(name, old))
        # New proof sources have current objects; historical object hashes do not apply.
        assert json.loads((args.build_directory / (name + '.json')).read_bytes()) == row
        for relative, digest, size in output_members(name, row):
            path = args.build_directory / relative
            assert path.resolve().is_relative_to(args.build_directory.resolve())
            assert path.is_file() and (size is None or path.stat().st_size == size)
            with path.open('rb') as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
            byte_count += path.stat().st_size
    print(json.dumps({
        'status': 'FAST40_STAGED_STANDARD_KERNEL_EXPORTS_VERIFIED',
        'endpoint': PREFIX, 'required_modules': 92, 'fresh_modules': 14,
        'unchanged_historical_objects_reproduced': 5, 'new_source_bound_exports': 9,
        'original_data_preserved_verbatim': True, 'public_acceptance_type_preserved': True,
        'acceptance_proof_body_changed': True, 'cell008_source_closure_preserved': True,
        'standard_axioms_only': True, 'verified_fresh_output_bytes': byte_count,
        'full_degree_one_large_closure': 'PENDING_SEPARATE_FINAL_ASSEMBLY',
    }), flush=True)


if __name__ == '__main__':
    main()

