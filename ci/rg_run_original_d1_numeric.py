"""Run one sealed exact original numeric batch with the existing strict tools."""
import argparse, json, os, pathlib, re, subprocess, sys
from rg_original_d1_numeric_reproduction import load_plan, ROOT, SOURCES

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--plan', type=pathlib.Path, required=True)
p.add_argument('--phase', choices=('materialize', 'cache', 'kernel'), required=True)
a = p.parse_args()
plan, _ = load_plan(a.plan)
if a.phase == 'materialize':
    if plan['tag'] in ('00', '30'):
        producer = json.loads((ROOT / 'ci/rg_shared_arm_materialization_plan.json').read_bytes())
        if plan['chunk'] in producer['classes'][plan['tag']]['open_chunk_indices']:
            subprocess.run([sys.executable, '-B', 'ci/rg_materialize_shared_arm.py',
                            '--tag', plan['tag'], '--chunk', str(plan['chunk'])], cwd=ROOT, check=True)
        else:
            # Checked-in immutable chunks are never sent to the open-source
            # producer. Their existing bytes must match the same strict rows.
            for name in plan['fresh_module_origins']:
                assert (SOURCES / (name.replace('.', '/') + '.lean')).is_file(), name
    subprocess.run([sys.executable, '-B', 'ci/rg_original_d1_numeric_reproduction.py',
                    '--plan', str(a.plan), '--phase', 'source-plan'], cwd=ROOT, check=True)
elif a.phase == 'cache':
    sys.path.insert(0, str(SOURCES))
    from verify import without_comments
    seen, external = set(), set()
    def visit(n):
        if n in seen: return
        seen.add(n)
        base = SOURCES / 'ThirdParty/LeanCert' if n.startswith('LeanCert.') else SOURCES
        text = without_comments((base / (n.replace('.', '/') + '.lean')).read_text())
        for d in re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)\s*$', text, re.M):
            if d.startswith(('Proofs.', 'LeanCert.')): visit(d)
            elif not d.startswith(('Lean.', 'Init.', 'Std.')) and d not in ('Lean', 'Init', 'Std'): external.add(d)
    for endpoint in plan['endpoints']: visit(endpoint)
    subprocess.run(['lake', 'exe', 'cache', 'get', *sorted(external)], cwd=ROOT, check=True)
else:
    command = [sys.executable, '-B', 'ci/rg_observed_kernel_verify.py',
               '--memory-reserve-mib', '2048', '--', '--mathlib-project', str(ROOT)]
    for endpoint in plan['endpoints']: command.extend(['--endpoint', endpoint])
    command.extend(['--workers', str(plan['workers']), '--module-timeout', '1200', '--resume'])
    subprocess.run(command, cwd=ROOT, check=True)
