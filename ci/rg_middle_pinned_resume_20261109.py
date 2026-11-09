#!/usr/bin/env python3
"""Prepare exact source-bound continuations from digest-pinned original archives.

This creates no proof. The existing authenticated restore tools and fresh Lean
kernel verifier remain mandatory. Historical exports retain their real origin.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SCOPE = ROOT / 'Proofs/RG_Lean_20261019'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PREFIX = 'Proofs.RadenkovicGutman'
NEW = PREFIX + 'MiddleAnchor270MeanReserve'
COMMON = [
    'ci/rg_middle_generic_recovery_20261104_run41805266301_prior_exports.json',
    'ci/rg_middle_original_integer_payment_generic_prior_exports.json',
    'ci/rg_middle_oct27_anchor028_parts_original_partial_prior_exports.json',
    'ci/rg_middle_oct28_anchor028_original_prior_exports.json',
]
CONFIG = {
    '270': dict(artifact_id=13566531449,
        artifact_sha256='4cc31db8a6d19170e7c6c752a8a7266cb5fa9510501343908d62c53e554d72fd',
        run=42345329502, job=128321707343,
        source_commit='12d2d0ddecb59686244f7eb14c42687ec2b456e9', count=35),
    '512': dict(artifact_id=12999751917,
        artifact_sha256='30be8228d629aa76c7258fc34cbec02b0c570c154defdbf11520e4203e74c755',
        run=40714530693, job=122908481615,
        source_commit='b5648d132318fe3d955f1ebe79ed333a58abc722', count=116),
}

def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)

def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()

def unique(pairs):
    out = {}
    for key, value in pairs:
        need(key not in out, 'Duplicate JSON key: ' + key)
        out[key] = value
    return out

def load(raw: bytes):
    return json.loads(raw, object_pairs_hook=unique)

class StripAuthRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        result = super().redirect_request(req, fp, code, msg, headers, newurl)
        if result is not None:
            result.remove_header('Authorization')
        return result

def archive_bytes(config: dict, local: Path | None) -> bytes:
    if local is not None:
        raw = local.read_bytes()
    else:
        url = ('https://api.github.com/repos/RhudeJJJJ/formal-conjectures/'
               f"actions/artifacts/{config['artifact_id']}/zip")
        request = urllib.request.Request(url, headers={
            'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'],
            'Accept': 'application/vnd.github+json',
            'X-GitHub-Api-Version': '2022-11-28',
        })
        with urllib.request.build_opener(StripAuthRedirect()).open(request, timeout=180) as response:
            raw = response.read(32 * 1024 * 1024)
    need(digest(raw) == config['artifact_sha256'], 'Original archive digest mismatch')
    return raw

def expected_frontier(target: str) -> list[str]:
    if target == '270':
        return [NEW]
    return sorted([PREFIX + f'WideAnchor512Cell{i:03d}' for i in range(95, 134)] +
        [PREFIX + f'WideAnchor512Batch{i:03d}' for i in range(9, 14)] +
        [PREFIX + 'WideAnchor512FinitePayment', PREFIX + 'WideAnchor512OriginalAnchor',
         PREFIX + 'MiddleOriginalAnchorCertificate512'])

def prepare(target: str, local: Path | None) -> dict:
    config = CONFIG[target]
    raw = archive_bytes(config, local)
    z = zipfile.ZipFile(io.BytesIO(raw))
    need(len(z.namelist()) == len(set(z.namelist())), 'Duplicate ZIP names')
    original = load(z.read('generated_source/generated_source_manifest.json'))
    original_endpoint = PREFIX + 'MiddleOriginalAnchorCertificate' + target
    need(original['endpoint'] == original_endpoint, 'Wrong original endpoint')
    sources = original['source_sha256'].copy()
    need(len(sources) == 281, 'Changed original closure size')
    out = SCOPE / 'build/fresh_exports'
    hashes = {}
    for rel, value in sources.items():
        path = (ROOT / rel).resolve()
        need(path.is_relative_to(SCOPE.resolve()) and rel.endswith('.lean'), 'Unsafe source path')
        code = z.read('generated_source/' + rel)
        need(digest(code) == value == digest(path.read_bytes()), 'Original source changed: ' + rel)
        module = rel.removeprefix('Proofs/RG_Lean_20261019/').removesuffix('.lean').replace('/', '.')
        need(module.startswith('Proofs.'), 'Unexpected source module')
        hashes[module] = value
        destination = out / 'generated_source' / rel
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(code)
    records = load(z.read('diagnostics_records.json'))['modules']
    need(len({r['module'] for r in records}) == len(records), 'Duplicate module records')
    fresh = {r['module']: r for r in records if r['mode'] == 'FRESH_KERNEL_EXPORT'}
    need(len(fresh) == config['count'], 'Changed original fresh export count')
    for module, row in fresh.items():
        need(row['source_sha256'] == hashes[module], 'Fresh export source mismatch')
        need(row['axiom_profiles'] and all(set(a) <= ALLOWED for a in row['axiom_profiles']),
             'Unexpected axiom profile')
        need(not row.get('additional_outputs'), 'Unexpected object sidecar')
        need(digest(z.read(module.replace('.', '/') + '.olean')) == row['output_sha256'],
             'Fresh original object mismatch')
    if target == '270':
        receipt = load(z.read('receipt.json'))
        need(receipt['endpoints'] == [original_endpoint], 'Wrong complete receipt')
        need(receipt['mathlib'] == PIN and receipt['leancert'] == LC, 'Wrong receipt pins')
        need(set(receipt['modules']) == set(hashes), 'Receipt/source closure mismatch')
        by_name = {row['module']: row for row in records}
        for module, row in receipt['modules'].items():
            need(row == by_name.get(module), 'Receipt/diagnostics mismatch')
    manifest = {k: v for k, v in config.items() if k != 'count'}
    manifest.update(repository='RhudeJJJJ/formal-conjectures', lean_version='4.33.1',
        mathlib=PIN, leancert=LC, modules=fresh,
        kind='ORIGINAL_FRESH_EXPORTS_FROM_DIGEST_PINNED_ARCHIVE')
    generated = ROOT / 'ci' / ('_rg_pinned_' + target + '_20261109')
    generated.mkdir(parents=True, exist_ok=True)
    manifest_path = generated / 'original_fresh_exports.json'
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    plan = COMMON.copy()
    if target == '270':
        plan.append('ci/rg_middle_anchor270_run40714530693_partial_prior_exports.json')
    plan.append(str(manifest_path.relative_to(ROOT)))
    (generated / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    endpoint = NEW if target == '270' else original_endpoint
    if target == '270':
        rel = 'Proofs/RG_Lean_20261019/' + NEW.replace('.', '/') + '.lean'
        sources[rel] = digest((ROOT / rel).read_bytes())
        destination = out / 'generated_source' / rel
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, destination)
    lock = dict(endpoint=endpoint, original_endpoint=original_endpoint,
        source_sha256=sources, original_artifact=config, fresh_frontier=expected_frontier(target))
    (generated / 'source_lock.json').write_text(json.dumps(lock, indent=2) + '\n')
    (out / 'source_lock.json').write_text(json.dumps(lock, indent=2) + '\n')
    (out / 'generated_source/generated_source_manifest.json').write_text(json.dumps(dict(
        endpoint=endpoint, source_sha256=sources,
        kind='SOURCE_LOCK_REQUIRES_FRESH_KERNEL_RECEIPT'), indent=2) + '\n')
    return lock

def check_frontier(target: str) -> None:
    lock = load((ROOT / 'ci' / ('_rg_pinned_' + target + '_20261109') / 'source_lock.json').read_bytes())
    for rel, value in lock['source_sha256'].items():
        need(digest((ROOT / rel).read_bytes()) == value, 'Source changed after preparation')
    plan = load((SCOPE / 'build/extension/bounded_kernel_fallback_plan.json').read_bytes())
    need(plan['endpoint'] == lock['endpoint'], 'Wrong verified frontier endpoint')
    need(plan['required_modules'] == len(lock['source_sha256']), 'Wrong full closure size')
    need(sorted(plan['fresh_modules']) == expected_frontier(target) == lock['fresh_frontier'],
         'Wrong exact fresh module identities')
    need(plan['verified_prior_objects'] + len(plan['fresh_modules']) == plan['required_modules'],
         'Incomplete frontier partition')
    print(json.dumps({**plan, 'status': 'EXACT_SOURCE_AND_FRONTIER_NOT_A_PROOF'}))

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target', choices=sorted(CONFIG))
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--check-frontier', action='store_true')
    args = parser.parse_args()
    if args.check_frontier:
        check_frontier(args.target)
    else:
        lock = prepare(args.target, args.archive)
        print(json.dumps(dict(status='PINNED_ORIGINAL_SOURCES_PREPARED_NOT_A_PROOF',
            endpoint=lock['endpoint'], sources=len(lock['source_sha256']),
            mandatory_fresh=len(lock['fresh_frontier']))))

if __name__ == '__main__':
    main()
