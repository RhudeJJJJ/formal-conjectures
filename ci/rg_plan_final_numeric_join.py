"""Plan the sealed two historical heads followed by the three final modules.

Only these five named sources may need fresh kernel exports. Historical heads
must later match their original binary identities. The final three-module
frontier is independently checked after the two heads have been reconstructed.
"""
import argparse, json, pathlib
from rg_plan_exact_degree_one_large import source_closure, matching_archives, plan, FRESH

ROOT = pathlib.Path(__file__).resolve().parents[1]
HEADS = {'Proofs.RadenkovicGutmanD1Long10', 'Proofs.RadenkovicGutmanD1Long30'}
ENDPOINT = 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--output', type=pathlib.Path, required=True)
a = p.parse_args()
spec = json.loads((ROOT / 'ci/rg_d1_required_numeric_batches_20261103.json').read_bytes())
hashes, dependencies, closures = source_closure(ENDPOINT)
assert hashes[ENDPOINT] == spec['source_endpoint_sha256']
assert closures[ENDPOINT] == spec['source_endpoint_closure_sha256']
assert len(hashes) == spec['required_modules']
report = plan(ENDPOINT, hashes, dependencies, closures, matching_archives(hashes, closures),
              fresh_allowlist=set(FRESH) | HEADS)
a.output.parent.mkdir(parents=True, exist_ok=True)
a.output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ('endpoint', 'required_modules', 'fresh_modules',
                                      'missing_original_modules', 'complete_original_object_coverage')}), flush=True)
assert not report['missing_original_modules'], 'Missing original prerequisite archives; final kernel run remains blocked'
assert set(report['fresh_modules']) == set(FRESH) | HEADS
