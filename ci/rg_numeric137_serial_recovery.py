"""Repeat only the timed-out original batch137 with one compiler worker.

The original sealed ten-module plan and every historical source, closure,
object, axiom and member check are reused verbatim. Only process concurrency
changes; the module timeout and memory reserve remain fixed.
"""
import argparse, hashlib, json, pathlib, subprocess, sys
from rg_original_d1_numeric_reproduction import ROOT, SOURCES, load_plan

SPEC = ROOT / 'ci/rg_d1_numeric137_serial_20261103.json'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--phase', choices=('materialize', 'cache', 'preflight', 'kernel', 'compare'), required=True)
    a = p.parse_args()
    spec = json.loads(SPEC.read_bytes())
    assert spec['kind'] == 'EXACT_ORIGINAL_NUMERIC137_SERIAL_RECOVERY'
    assert spec['repository'] == 'RhudeJJJJ/formal-conjectures'
    assert (spec['original_run'], spec['original_job'], spec['original_source_commit']) == (
        41686621300, 126095228986, 'aaeaec3cec22467d3f0b83b1761bfb40087bb991')
    assert spec['original_batch'] == '00_137'
    assert (spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (1, 1200, 2048)
    relative = pathlib.Path(spec['original_plan'])
    assert relative == pathlib.Path('ci/rg_d1_required_numeric_batches_20261103/batch00_137.json')
    raw = (ROOT / relative).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == spec['original_plan_sha256'] == '87a9e926ba76df68fbf0d66c6c3d32273b4db143c0c24730f3f8aa652876e74a'
    plan, expected = load_plan(ROOT / relative)
    assert plan['scope'] == 'original00_leaves' and plan['tag'] == '00' and plan['chunk'] == 137
    names = [f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in range(1370, 1380)]
    assert plan['endpoints'] == spec['expected_fresh_modules'] == sorted(expected) == names
    out = SOURCES / 'build/fresh_exports'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'exact_serial_runtime_scope.json').write_text(json.dumps(spec, indent=2) + '\n')
    if a.phase in ('materialize', 'cache'):
        command = [sys.executable, '-B', 'ci/rg_run_original_d1_numeric.py',
                   '--plan', str(relative), '--phase', a.phase]
    elif a.phase in ('preflight', 'compare'):
        command = [sys.executable, '-B', 'ci/rg_original_d1_numeric_reproduction.py',
                   '--plan', str(relative), '--phase', a.phase]
    else:
        command = [sys.executable, '-B', 'ci/rg_observed_kernel_verify.py',
                   '--memory-reserve-mib', '2048', '--', '--mathlib-project', str(ROOT)]
        for endpoint in names:
            command.extend(['--endpoint', endpoint])
        command.extend(['--workers', '1', '--module-timeout', '1200', '--resume'])
    subprocess.run(command, cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
