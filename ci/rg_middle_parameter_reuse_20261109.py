"""Restore the fixed successful parameter-coverage producer; never call it fresh."""
from __future__ import annotations
import argparse
import hashlib
import io
import json
import pathlib
import subprocess
import sys
import zipfile

META = {
    'repository': 'RhudeJJJJ/formal-conjectures',
    'run': 42704252628,
    'job': 129456735506,
    'source_commit': '317f7373b45a6803b0feebb24f14e771ecc72ea5',
    'artifact_id': 13713931433,
    'artifact_sha256': '3773983b5bfda8b08d93df9caa79750757e3be8073f4b2e421d6900bbdc80bc2',
    'lean_version': '4.33.1',
    'mathlib': '0df444a360eaa60ab8c11dca51a86af692955474',
    'leancert': '621a43d7cf21f87872392a01e874f2f1dbddc926',
}
MANIFEST_SHA256 = 'bfe4e6eba769cb046a8c4ce111f5074082246b41bfb2dc7e0f28f36b5db1fe4b'
ENDPOINT = 'Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverageComplete'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}


def manifest_from_archive(raw: bytes) -> dict:
    if hashlib.sha256(raw).hexdigest() != META['artifact_sha256']:
        raise ValueError('Wrong original archive bytes')
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError('Duplicate archive members')
        receipt = json.loads(archive.read('receipt.json'))
        if receipt['endpoints'] != [ENDPOINT] or len(receipt['modules']) != 154:
            raise ValueError('Wrong complete source scope')
        if receipt['mathlib'] != META['mathlib'] or receipt['leancert'] != META['leancert']:
            raise ValueError('Wrong dependency pins')
        if 'version 4.33.1,' not in receipt['lean']:
            raise ValueError('Wrong Lean version')
        fresh = {n: r for n, r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
        if len(fresh) != 114:
            raise ValueError('Wrong fresh-module set')
        for name, row in fresh.items():
            if row != json.loads(archive.read(name + '.json')):
                raise ValueError('Receipt/export mismatch: ' + name)
            if not row['axiom_profiles'] or any(set(p) - ALLOWED for p in row['axiom_profiles']):
                raise ValueError('Nonstandard axioms: ' + name)
            obj = archive.read(name.replace('.', '/') + '.olean')
            if hashlib.sha256(obj).hexdigest() != row['output_sha256']:
                raise ValueError('Wrong compiled object: ' + name)
        manifest = dict(META, modules=fresh)
        canonical = json.dumps(manifest, sort_keys=True, separators=(',', ':')).encode()
        if hashlib.sha256(canonical).hexdigest() != MANIFEST_SHA256:
            raise ValueError('Manifest differs from the independently audited records')
        return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=pathlib.Path)
    parser.add_argument('--restore', action='store_true')
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[1]
    build = root / 'Proofs/RG_Lean_20261019/build'
    if args.archive is None:
        sys.path.insert(0, str(root / 'Proofs/RG_Lean_20261019'))
        from rg_github_artifacts import fetch_archive
        raw = fetch_archive(META)
    else:
        raw = args.archive.read_bytes()
    manifest = manifest_from_archive(raw)
    reuse = build / 'parameter_coverage_reuse'
    reuse.mkdir(parents=True, exist_ok=True)
    archive = reuse / 'original.zip'
    archive.write_bytes(raw)
    path = reuse / 'prior_exports.json'
    path.write_text(json.dumps(manifest, indent=2) + '\n')
    if args.restore:
        subprocess.run([
            sys.executable, '-B', str(root / 'ci/rg_restore_job_exports.py'),
            '--manifest', str(path), '--build-directory', str(build / 'extension'),
            '--verified-local-archive', str(archive),
        ], cwd=root, check=True)
    print(json.dumps({'status': 'PINNED_ORIGINAL_PARAMETER_EXPORTS_AUTHENTICATED_NOT_FRESH',
                      'run': META['run'], 'artifact_id': META['artifact_id'], 'modules': 114,
                      'restored': args.restore, 'current_source_closure_requires_verifier': True}))


if __name__ == '__main__':
    main()
