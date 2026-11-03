"""Plan exact missing original numeric exports from an authenticated preflight.

Each job keeps the original sources and historical output identities. Class00
jobs contain at most ten actual leaf endpoints. Class10/30 jobs contain one
original chunk and at most sixteen missing modules beyond the retained base.
The two original class heads are checked separately before the final three.
"""
import argparse, hashlib, json, pathlib, re

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
BASE = 'ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json'
LEAF = re.compile(r'Proofs\.RadenkovicGutmanD1Long00Leaf(\d{5})')
HEADS = ['Proofs.RadenkovicGutmanD1Long10', 'Proofs.RadenkovicGutmanD1Long30']


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def identity(row):
    return {k: row.get(k) for k in ('module', 'source_sha256', 'source_closure_sha256',
                                   'output_sha256', 'axiom_profiles', 'additional_outputs')}


def build(scope, manifests):
    assert scope['kind'] == 'EXACT_SOURCE_BOUND_COMPRESSED_RESTORE_PLAN'
    assert scope['endpoint'] == 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
    assert scope['mathlib'] == PIN and scope['leancert'] == LC
    missing = set(scope['missing_original_modules'])
    base = manifests[BASE]
    assert base['data']['kind'] == 'INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE'
    base_names = set(base['data']['modules'])
    indexed = {}
    for relative, descriptor in sorted(manifests.items()):
        data = descriptor['data']
        if data.get('mathlib') != PIN or data.get('lean_version') != '4.33.1':
            continue
        for name, row in data.get('modules', {}).items():
            if name not in missing or row.get('mode') != 'FRESH_KERNEL_EXPORT':
                continue
            if row.get('source_sha256') != scope['source_sha256'][name] or row.get('source_closure_sha256') != scope['source_closure_sha256'][name]:
                continue
            if name in indexed:
                assert identity(indexed[name][1]) == identity(row), ('Conflicting historical identities', name)
            else:
                indexed[name] = (relative, row)
    def closure(endpoint):
        seen = set()
        def visit(n):
            if n in seen: return
            seen.add(n)
            for d in scope['source_dependencies'][n]: visit(d)
        visit(endpoint)
        return seen
    def specification(kind, tag, chunk, endpoints, fresh):
        assert fresh <= missing and 1 <= len(fresh) <= 16
        assert fresh <= indexed.keys(), sorted(fresh - indexed.keys())
        origins = {n: indexed[n][0] for n in sorted(fresh)}
        return {
            'kind': 'EXACT_ORIGINAL_D1_NUMERIC_REPRODUCTION', 'scope': kind,
            'tag': tag, 'chunk': chunk, 'endpoints': endpoints,
            'workers': 1 if kind == 'original_long_heads' else 2,
            'memory_reserve_mib': 2048, 'module_timeout': 1200,
            'base_manifest': BASE, 'base_manifest_sha256': base['sha256'],
            'original_manifests': {p: manifests[p]['sha256'] for p in sorted(set(origins.values()))},
            'fresh_module_origins': origins,
        }
    jobs = []
    grouped = {}
    for n in sorted(missing):
        if match := LEAF.fullmatch(n):
            grouped.setdefault(int(match[1]) // 10, []).append(n)
    for chunk, endpoints in sorted(grouped.items()):
        fresh = set(endpoints)
        assert set().union(*(closure(n) for n in endpoints)) - base_names == fresh
        jobs.append({'batch': f'00_{chunk:03d}', 'spec': specification('original00_leaves', '00', chunk, endpoints, fresh)})
    for tag in ('10', '30'):
        pattern = re.compile(r'Proofs\.RadenkovicGutmanD1Long' + tag + r'Chunk(\d{3})')
        for endpoint in sorted(missing):
            if match := pattern.fullmatch(endpoint):
                fresh = closure(endpoint) - base_names
                assert all(re.fullmatch(r'Proofs\.RadenkovicGutmanD1Long' + tag + r'(?:Leaf\d{5}|Cells\d{4}|Chunk\d{3})', n) for n in fresh)
                jobs.append({'batch': f'{tag}_{int(match[1]):03d}', 'spec': specification('original_long_chunk', tag, int(match[1]), [endpoint], fresh)})
    covered = set()
    for item in jobs:
        names = set(item['spec']['fresh_module_origins'])
        assert not covered.intersection(names), item['batch']
        covered.update(names)
        item['historical_module_elapsed_seconds'] = round(sum(indexed[n][1]['seconds'] for n in names), 3)
    numeric = {n for n in missing if LEAF.fullmatch(n) or re.fullmatch(r'Proofs\.RadenkovicGutmanD1Long(?:10|30)(?:Leaf\d{5}|Cells\d{4}|Chunk\d{3})', n)}
    assert covered == numeric
    # Larger measured historical batches start first, making real heavy-case
    # resource failures visible early without adding speculative extra tests.
    jobs.sort(key=lambda item: (-item['historical_module_elapsed_seconds'], item['batch']))
    assert 256 < len(jobs) <= 512
    heads = specification('original_long_heads', '10_30', None, HEADS, set(HEADS))
    return {
        'kind': 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES', 'mathlib': PIN,
        'leancert': LC, 'lean_version': '4.33.1', 'endpoint': scope['endpoint'],
        'source_endpoint_sha256': scope['source_sha256'][scope['endpoint']],
        'source_endpoint_closure_sha256': scope['source_closure_sha256'][scope['endpoint']],
        'required_modules': scope['required_modules'], 'jobs': jobs, 'head_spec': heads,
        'scheduled_numeric_modules': sorted(covered), 'staged_head_modules': HEADS,
        'other_missing_prerequisites': sorted(missing - covered - set(HEADS)),
        'maximum_parallel_numeric_jobs': 8, 'matrix_wave_limit': 256,
        'proof_status': 'SOURCE_IDENTICAL_RECONSTRUCTION_PLAN_REQUIRES_KERNEL_AND_FULL_FINAL_JOIN',
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--scope-plan', type=pathlib.Path, required=True)
    p.add_argument('--manifest-root', type=pathlib.Path, action='append', required=True)
    p.add_argument('--output-root', type=pathlib.Path, required=True)
    a = p.parse_args()
    manifests = {}
    for root in a.manifest_root:
        for path in sorted((root / 'ci').rglob('*.json')):
            raw = path.read_bytes()
            data = json.loads(raw)
            if isinstance(data, dict) and isinstance(data.get('modules'), dict):
                relative = str(path.relative_to(root))
                assert relative not in manifests or manifests[relative]['sha256'] == sha(raw)
                manifests[relative] = {'data': data, 'sha256': sha(raw)}
    raw = a.scope_plan.read_bytes()
    result = build(json.loads(raw), manifests)
    result['source_scope_plan_sha256'] = sha(raw)
    out = a.output_root
    for index, item in enumerate(result['jobs']):
        relative = 'ci/rg_d1_required_numeric_batches_20261103/batch' + item['batch'] + '.json'
        path = out / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        spec = item.pop('spec')
        path.write_text(json.dumps(spec, indent=2) + '\n')
        item.update(plan=relative, plan_sha256=sha(path.read_bytes()), wave=index // 256 + 1)
    relative = 'ci/rg_d1_required_numeric_batches_20261103/long_heads.json'
    path = out / relative
    path.write_text(json.dumps(result.pop('head_spec'), indent=2) + '\n')
    result['head_plan'] = relative
    result['head_plan_sha256'] = sha(path.read_bytes())
    config = out / 'ci/rg_d1_required_numeric_batches_20261103.json'
    config.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'jobs': len(result['jobs']), 'modules': len(result['scheduled_numeric_modules']),
                      'heads': result['staged_head_modules'], 'other_missing': len(result['other_missing_prerequisites']),
                      'waves': [sum(j['wave'] == w for j in result['jobs']) for w in (1, 2)],
                      'largest_batches': result['jobs'][:8], 'source_scope_plan_sha256': result['source_scope_plan_sha256']}), flush=True)


if __name__ == '__main__':
    main()
