"""Reconstruct only the frozen original prerequisites of two closed RG families."""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

import rg_plan_exact_degree_one_large as exact

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Proofs/RG_Lean_20261019'
SPEC = ROOT / 'ci/rg_compact_closed_support_20261103.json'
SPEC_SHA256 = 'a8c6824514dc07e31fa7ce3c2c862c451dc88a894750a15be5203a8d65953f08'
sys.path.insert(0, str(SOURCE))
from module_outputs import output_members


def load_spec():
    raw = SPEC.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SPEC_SHA256
    spec = json.loads(raw)
    assert spec['kind'] == 'EXACT_COMPACT_CLOSED_ORIGINAL_SUPPORT_RECONSTRUCTION'
    assert spec['mathlib'] == exact.PIN and spec['leancert'] == exact.LC
    assert spec['lean_version'] == '4.33.1'
    assert spec['workers'] == 1 and spec['memory_reserve_mib'] == 2048
    assert spec['module_timeout'] == 900
    assert len(spec['historical_rows']) == 673 and len(spec['root_batches']) == 17
    roots = [name for batch in spec['root_batches'].values() for name in batch['endpoints']]
    assert len(roots) == len(set(roots)) == 530
    assert all(1 <= len(batch['endpoints']) <= 32 for batch in spec['root_batches'].values())
    assert len(spec['support_modules']) == len(set(spec['support_modules'])) == 143
    assert not set(roots).intersection(spec['support_modules'])
    assert set(roots).union(spec['support_modules']) == set(spec['historical_rows'])
    for key in ('base_manifest', 'common_manifest'):
        relative = pathlib.Path(spec[key])
        assert relative.is_relative_to('ci') and '..' not in relative.parts
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == spec[key + '_sha256']
    return spec


def scope(spec, stage, batch):
    if stage == 'roots':
        assert batch in spec['root_batches']
        endpoints = spec['root_batches'][batch]['endpoints']
        expected = set(endpoints)
    else:
        assert batch is None
        endpoints = spec['support_endpoints']
        expected = set(spec['support_modules'])
    hashes, closures = {}, {}
    for endpoint in endpoints:
        found, _, recursive = exact.source_closure(endpoint)
        for name in found:
            assert name not in hashes or hashes[name] == found[name]
            assert name not in closures or closures[name] == recursive[name]
            hashes[name], closures[name] = found[name], recursive[name]
    for name in expected:
        old = spec['historical_rows'][name]
        assert old['module'] == name and old['mode'] == 'FRESH_KERNEL_EXPORT'
        assert old['axiom_profiles'] and all(set(p) <= exact.ALLOWED for p in old['axiom_profiles'])
        assert hashes[name] == old['source_sha256'], ('Changed original source', name)
        assert closures[name] == old['source_closure_sha256'], ('Changed original closure', name)
    return endpoints, expected, hashes, closures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', choices=('roots', 'support'), required=True)
    parser.add_argument('--batch')
    parser.add_argument('--phase', choices=('source-plan', 'preflight', 'run', 'compare'), required=True)
    args = parser.parse_args()
    spec = load_spec()
    endpoints, expected, hashes, closures = scope(spec, args.stage, args.batch)
    build = SOURCE / 'build/extension'
    output = SOURCE / 'build/fresh_exports'
    output.mkdir(parents=True, exist_ok=True)
    report = {
        'stage': args.stage, 'batch': args.batch, 'endpoints': endpoints,
        'required_modules': len(hashes), 'fresh_modules': sorted(expected),
        'spec_sha256': SPEC_SHA256,
    }
    if args.phase == 'source-plan':
        report['status'] = 'EXACT_HISTORICAL_COMPACT_SUPPORT_SOURCES_MATCH_NO_PROOF'
    elif args.phase == 'preflight':
        actual = set()
        for endpoint in endpoints:
            subprocess.run([
                sys.executable, '-B', str(ROOT / 'ci/rg_restore_with_kernel_fallback.py'),
                '--plan', 'ci/rg_empty_restore_plan.json', '--build-directory', str(build),
                '--endpoint', endpoint, '--max-fresh', str(len(expected)), '--preflight-only',
            ], cwd=ROOT, check=True)
            frontier = json.loads((build / 'bounded_kernel_fallback_plan.json').read_bytes())
            assert frontier['within_bound'] is True
            fresh = set(frontier['fresh_modules'])
            assert fresh <= expected, ('Unexpected original support frontier', sorted(fresh - expected))
            if args.stage == 'roots':
                assert fresh == {endpoint}
            actual.update(fresh)
        assert actual == expected
        report['status'] = 'EXACT_COMPACT_SUPPORT_FRONTIER_REQUIRES_KERNEL'
    elif args.phase == 'run':
        command = [
            sys.executable, '-B', 'ci/rg_observed_kernel_verify.py',
            '--memory-reserve-mib', str(spec['memory_reserve_mib']), '--',
            '--mathlib-project', str(ROOT),
        ]
        for endpoint in endpoints:
            command.extend(('--endpoint', endpoint))
        command.extend(('--workers', str(spec['workers']),
                        '--module-timeout', str(spec['module_timeout']), '--resume'))
        subprocess.run(command, cwd=ROOT, check=True)
        return
    else:
        receipt = json.loads((build / 'receipt.json').read_bytes())
        assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE'
        assert len(receipt['endpoints']) == len(endpoints) and set(receipt['endpoints']) == set(endpoints)
        assert receipt['mathlib'] == exact.PIN and receipt['leancert'] == exact.LC
        assert 'version 4.33.1,' in receipt['lean']
        assert set(receipt['modules']) == set(hashes)
        fresh = {name: row for name, row in receipt['modules'].items() if row['mode'] == 'FRESH_KERNEL_EXPORT'}
        assert set(fresh) == expected
        logical = 0
        for name, row in receipt['modules'].items():
            assert row['module'] == name
            assert row['source_sha256'] == hashes[name] and row['source_closure_sha256'] == closures[name]
            assert row['axiom_profiles'] and all(set(p) <= exact.ALLOWED for p in row['axiom_profiles'])
        for name, row in fresh.items():
            old = spec['historical_rows'][name]
            assert row == json.loads((build / (name + '.json')).read_bytes())
            for key in ('module', 'source_sha256', 'source_closure_sha256', 'output_sha256', 'axiom_profiles'):
                assert row[key] == old[key], ('Changed historical output identity', name, key)
            members = tuple(sorted(output_members(name, row)))
            assert members == tuple(sorted(output_members(name, old))), ('Changed output members', name)
            for relative, digest, size in members:
                path = build / relative
                assert path.resolve().is_relative_to(build.resolve()) and path.is_file()
                assert size is None or path.stat().st_size == size
                with path.open('rb') as stream:
                    assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest, (name, relative)
                logical += path.stat().st_size
        report.update(status='EXACT_HISTORICAL_COMPACT_SUPPORT_IDENTITIES_REPRODUCED',
                      verified_fresh_output_bytes=logical)
    (output / ('compact_support_' + args.phase.replace('-', '_') + '.json')).write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, separators=(',', ':')), flush=True)


if __name__ == '__main__':
    main()
