"""Plan two historical heads, two changed intervals, and three final modules.

Only these seven named sources may need fresh kernel exports. Historical heads
must later match their original binary identities. The interval and final
three-module frontier is independently checked after reconstructing both heads.
"""
import argparse, json, pathlib
from rg_plan_exact_degree_one_large import source_closure, matching_archives, plan, FRESH

ROOT = pathlib.Path(__file__).resolve().parents[1]
HEADS = {'Proofs.RadenkovicGutmanD1Long10', 'Proofs.RadenkovicGutmanD1Long30'}
ENDPOINT = 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--output', type=pathlib.Path, required=True)
p.add_argument('--current-source-binding', type=pathlib.Path)
a = p.parse_args()
spec_raw = (ROOT / 'ci/rg_d1_required_numeric_batches_20261103.json').read_bytes()
spec = json.loads(spec_raw)
current_binding = None
if a.current_source_binding:
    from rg_exact_final_source_binding import (read_binding, prepare_current_sources,
        validate_current_graph, INTERVAL_RECHECKS)
    binding, current_binding = read_binding(a.current_source_binding, spec_raw)
    prepare_current_sources(binding)
hashes, dependencies, closures = source_closure(ENDPOINT)
if current_binding:
    validate_current_graph(binding, spec, hashes, closures)
else:
    assert hashes[ENDPOINT] == spec['source_endpoint_sha256']
    assert closures[ENDPOINT] == spec['source_endpoint_closure_sha256']
    assert len(hashes) == spec['required_modules']
allowed = set(FRESH) | HEADS | (INTERVAL_RECHECKS if current_binding else set())
report = plan(ENDPOINT, hashes, dependencies, closures, matching_archives(hashes, closures),
              fresh_allowlist=allowed)
if current_binding:
    report['current_source_binding'] = current_binding
a.output.parent.mkdir(parents=True, exist_ok=True)
a.output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ('endpoint', 'required_modules', 'fresh_modules',
                                      'missing_original_modules', 'complete_original_object_coverage')}), flush=True)
assert not report['missing_original_modules'], 'Missing original prerequisite archives; final kernel run remains blocked'
assert set(report['fresh_modules']) == allowed
