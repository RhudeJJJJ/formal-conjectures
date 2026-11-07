#!/usr/bin/env python3
"""Authenticate the actual bounded residual ListAssembly run; never create a receipt."""
import argparse
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import zipfile

B = Path(__file__).resolve().parent
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
NAMED = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", re.S)


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique_pairs)


def read(path):
    return decode(path.read_bytes())


def table(rows):
    if isinstance(rows, dict):
        require(all(k == r['module'] for k, r in rows.items()), 'Wrong module dictionary key')
        return rows
    result = {}
    for row in rows:
        require(row['module'] not in result, 'Duplicate module row')
        result[row['module']] = row
    return result


def payloads(log, prefix):
    result = []
    for line in log.splitlines():
        line = re.sub(r'^\d{4}-\d\d-\d\dT\S+\s', '', line)
        line = re.sub(r'\x1b\[[0-9;]*m', '', line)
        if line.startswith(prefix):
            result.append(decode(line[len(prefix):]))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--actual', type=Path, default=B / 'actual')
    args = parser.parse_args()
    actual = args.actual
    binding = read(B / 'completion_binding.json')
    for relative, expected in binding['fixed_input_sha256'].items():
        require(sha((B / relative).read_bytes()) == expected, 'Changed fixed input: ' + relative)
    inventory = read(B / 'fixed_source_inventory.json')
    graph = read(B / 'fixed_source_graph.json')
    priors = table(read(B / 'expected_prior_rows.json'))
    required = set(inventory['modules'])
    fresh = set(inventory['fresh_checkpoint_modules'])
    endpoint = binding['endpoint']
    require(len(required) == 39 and len(fresh) == 8 and len(priors) == 193, 'Changed source frontier')
    require(set(priors) & required == set(inventory['candidate_prior_modules']), 'Changed inherited frontier')
    require(len(required & set(priors)) == 31 and not fresh & set(priors), 'Prior/fresh overlap')

    run, jobs, catalog = [read(actual / f) for f in ('run.json', 'jobs.json', 'artifacts.json')]
    require(run['id'] == binding['run'] and run['run_attempt'] == binding['attempt'], 'Wrong run')
    require(run['repository']['full_name'] == binding['repository'], 'Wrong repository')
    require(run['head_sha'] == binding['head_sha'] and run['head_branch'] == binding['branch'], 'Wrong run source')
    require(run['event'] == 'push' and run['path'] == binding['workflow'], 'Wrong workflow')
    require(jobs['total_count'] == len(jobs['jobs']) == 1, 'Wrong job scope')
    job = jobs['jobs'][0]
    require(job['id'] == binding['job'] and job['run_id'] == binding['run'], 'Wrong job')
    require(job['run_attempt'] == binding['attempt'] and job['name'] == binding['job_name'], 'Wrong job binding')
    require(job['head_sha'] == binding['head_sha'] and job['head_branch'] == binding['branch'], 'Wrong job source')
    require(run['status'] == job['status'] == 'completed', 'Native work not terminal')
    require(run['conclusion'] == job['conclusion'] == 'success', 'Native run/job did not succeed')
    require(job['completed_at'] and all(s['conclusion'] == 'success' for s in job['steps']), 'Unsuccessful native step')
    require(catalog['total_count'] == len(catalog['artifacts']) == 1, 'Unexpected native artifact count')
    meta = catalog['artifacts'][0]
    require(meta['name'] == binding['artifact_name'] and meta['expired'] is False, 'Wrong/unavailable artifact')
    require(meta['workflow_run']['id'] == binding['run'] and meta['workflow_run']['head_sha'] == binding['head_sha'], 'Wrong artifact origin')
    archive_path = actual / 'artifact.zip'
    require(archive_path.stat().st_size == meta['size_in_bytes'], 'Wrong archive size')
    with archive_path.open('rb') as stream:
        require(hashlib.file_digest(stream, 'sha256').hexdigest() == meta['digest'].removeprefix('sha256:'), 'Wrong archive digest')
    log = (actual / 'job.log').read_text()
    require(meta['digest'].removeprefix('sha256:') in log and str(meta['id']) in log, 'Native artifact upload binding missing')
    logged = table(payloads(log, 'COMPLETED_MODULE_JSON '))
    require(set(logged) == fresh, 'Actual fresh completed rows differ from fixed frontier')

    source_prefix = 'generated_source/Proofs/RG_Lean_20261019/'
    source_members = {source_prefix + n.replace('.', '/') + '.lean': n for n in required}
    expected = set(source_members) | {'generated_source/generated_source_manifest.json', 'diagnostics_records.json', 'resource_observer.json', 'receipt.json'}
    for name in fresh:
        expected.update({name.replace('.', '/') + '.olean', name + '.json', name + '.log'})
    require(len(expected) == 67, 'Wrong expected archive scope')
    with zipfile.ZipFile(archive_path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)) == 67 and set(names) == expected, 'Unexpected actual archive scope')
        for name in names:
            path = PurePosixPath(name)
            require(not path.is_absolute() and '..' not in path.parts and '\\' not in name and not archive.getinfo(name).is_dir(), 'Unsafe archive member')
        for path, name in source_members.items():
            require(sha(archive.read(path)) == graph['source_sha256'][name], 'Changed actual source: ' + name)
        manifest = decode(archive.read('generated_source/generated_source_manifest.json'))
        require(manifest['endpoint'] == endpoint and manifest['component_kind'] == binding['component_kind'], 'Wrong source manifest scope')
        require(manifest['kind'] == 'ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT', 'Wrong source manifest kind')
        require(manifest['source_sha256'] == {'Proofs/RG_Lean_20261019/' + n.replace('.', '/') + '.lean': graph['source_sha256'][n] for n in required}, 'Wrong source manifest hashes')
        diagnostics = table(decode(archive.read('diagnostics_records.json'))['modules'])
        require(set(diagnostics) == set(priors) | fresh and len(diagnostics) == 201, 'Wrong diagnostic scope')
        require(all(diagnostics[n] == row for n, row in priors.items()), 'Changed inherited original proof row/origin')
        checked = {}
        for name in sorted(fresh):
            row = diagnostics[name]
            require(row == logged[name] == decode(archive.read(name + '.json')), 'Native/archive fresh row mismatch')
            require(row['mode'] == 'FRESH_KERNEL_EXPORT' and 'origin' not in row and 'transport_capsule' not in row, 'Fresh export provenance changed')
            require(row['source_sha256'] == graph['source_sha256'][name] and row['source_closure_sha256'] == graph['source_closure_sha256'][name], 'Wrong fresh source identity')
            require(type(row['seconds']) in (int, float) and math.isfinite(row['seconds']) and row['seconds'] >= 0, 'Invalid module duration')
            require(not row.get('additional_outputs'), 'Unretained module sidecars')
            object_path = name.replace('.', '/') + '.olean'
            require(sha(archive.read(object_path)) == row['output_sha256'], 'Wrong fresh object bytes')
            module_log = archive.read(name + '.log').decode()
            require(not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', module_log), 'Module warning/error')
            matches = list(NAMED.finditer(module_log))
            require([m[1] for m in matches] == inventory['named_axiom_declarations'][name], 'Wrong ordered named axiom checks')
            profiles = [sorted(set(a.strip() for a in (m[2] or '').split(',') if a.strip())) for m in matches]
            require(all(set(p) <= ALLOWED for p in profiles), 'Unapproved theorem axiom')
            grouped = [p for m, p in zip(matches, profiles) if m[2] is not None] + [p for m, p in zip(matches, profiles) if m[2] is None]
            require(grouped == row['axiom_profiles'] and grouped, 'Record/named profiles mismatch')
            checked[name] = dict(row=row, output_bytes=archive.getinfo(object_path).file_size, named_axiom_profiles=[dict(declaration=m[1], axioms=p) for m, p in zip(matches, profiles)])
        require(sum(len(x['named_axiom_profiles']) for x in checked.values()) == 28, 'Missing named axiom checks')
        receipt_raw = archive.read('receipt.json')
        receipt = decode(receipt_raw)
        require(receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == [endpoint], 'Wrong completed endpoint')
        require(receipt['mathlib'] == inventory['mathlib_pin'] and receipt['leancert'] == inventory['leancert_pin'] and 'version 4.33.1,' in receipt['lean'], 'Wrong compiler/dependency pin')
        require(receipt['global_rg'] == 'NOT_PROVED' and receipt['complete_submission'] == 'NOT_SUBMITTED', 'Overstated receipt')
        rows = table(receipt['modules'])
        require(set(rows) == required and all(rows[n] == diagnostics[n] for n in required), 'Incomplete 39-module receipt')
        resource = decode(archive.read('resource_observer.json'))
        require(payloads(log, 'RG_KERNEL_RESOURCE_RESULT ') == [{k: v for k, v in resource.items() if k != 'samples'}], 'Observer result differs from native log')
        require(payloads(log, 'RG_KERNEL_RESOURCE_OBSERVATION ') == resource['samples'], 'Observer samples differ')
        require(resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == 0 and resource['mathlib_and_lean_flags_unchanged'] is True and resource['samples'], 'Observer did not complete')
        require(not payloads(log, 'RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY '), 'Memory guard stopped verifier')
        require(all(type(s['available_bytes']) is int and s['available_bytes'] >= 2048 * 1024**2 for s in resource['samples'] if s['lean_processes']), 'Observed memory reserve violation')
        require(resource['maximum_aggregate_lean_rss'] >= max(s['aggregate_lean_rss'] for s in resource['samples']), 'Invalid resource maximum')
    report = dict(status='ACTUAL_ORIGINAL_RESIDUAL_LIST_ASSEMBLY_AUTHENTICATED', repository=binding['repository'], run=binding['run'], job=binding['job'], head_sha=binding['head_sha'], endpoint=endpoint, native_conclusion='success', artifact={k: meta[k] for k in ('id','name','size_in_bytes','digest')}, required_modules=39, prior_modules=31, fresh_modules=8, named_axiom_profiles=28, receipt_sha256=sha(receipt_raw), binding_sha256=sha((B/'completion_binding.json').read_bytes()), authenticator_sha256=sha(Path(__file__).read_bytes()), modules=checked, fresh_output_bytes=sum(x['output_bytes'] for x in checked.values()), component_completed=True, middle_family_completed=False, global_rg_proved=False, remaining_original_families=3, kernel_receipt_created_by_authenticator=False, resource_seconds=resource['seconds'])
    output = actual / 'completion_authentication.json'
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'modules'}, indent=2))


if __name__ == '__main__':
    main()
