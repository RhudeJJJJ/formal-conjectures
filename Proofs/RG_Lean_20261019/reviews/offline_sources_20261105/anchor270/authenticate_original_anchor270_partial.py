#!/usr/bin/env python3
"""Fixed, offline validation of actual original Anchor270 partial producer evidence.

Utility parsers below are copied verbatim from the frozen and executed
Anchor029 continuation authenticator (SHA256 5ea66b63d162ae70eb84b9925b87027016d489cf8b0f277144637b65e41469d5).
No network access, restoration, Lean invocation or production receipt creation.
"""
import argparse, ast, hashlib, json, math, pathlib, re, sys, zipfile
HERE = pathlib.Path(__file__).resolve().parent
BASE = HERE.parent
ACTUAL = HERE / 'actual'
REPOSITORY = 'RhudeJJJJ/formal-conjectures'
RUN, JOB, ATTEMPT = 40714530693, 122908481481, 1
COMMIT = 'b5648d132318fe3d955f1ebe79ed333a58abc722'
SOURCE_COMMIT = '5aed41513a76d7d22be5087091e796587353bbf5'
BRANCH = 'rg-remaining-six-spectral-20261021'
WORKFLOW = '.github/workflows/rg-nine-original-anchors-verified-tail-decomposition-20261028.yml'
PLAN = 'ci/rg_nine_original_tail_parts_anchor270_restore_plan.json'
ENDPOINT = 'Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate270'
JOB_NAME = 'check (Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate270, ci/rg_nine_original_tail_parts_...'
ARTIFACT_ID = 12891755528
ARTIFACT_NAME = 'rg-nine-original-anchors-verified-tail-decomposition-20261028-exports-40714530693-2'
ARTIFACT_SHA = 'ef6ab324fbaec1259f6fa89fbb05185c28437fd8a2750f43b0ac21fec47d3f0f'
ARTIFACT_BYTES = 5861934
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ORIGIN_KEYS = ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')
BASE_MANIFEST = 'ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json'
EXPECTED_PLAN = [
 'ci/rg_middle_original_predicate_generic_prior_exports.json',
 'ci/rg_middle_original_integer_payment_generic_prior_exports.json',
 'ci/rg_middle_oct27_anchor028_parts_original_partial_prior_exports.json',
 'ci/rg_middle_oct28_anchor028_original_prior_exports.json',
]
KERNEL_STEP = 'Check multiplicities and actual graph spectral comparison'
KERNEL_COMMAND = ('python3 -B ci/rg_observed_kernel_verify.py --memory-reserve-mib 2048 -- '
 '--mathlib-project "$GITHUB_WORKSPACE" --endpoint ' + ENDPOINT +
 ' --workers 1 --module-timeout 600 --resume | python3 -B ci/rg_compact_ci_output.py')
SOURCE_PREFIX = 'generated_source/Proofs/RG_Lean_20261019/'
SOURCE_MANIFEST = 'generated_source/generated_source_manifest.json'
BAD_DIAGNOSTIC = re.compile(r"\b(error|warning)(?:\([^\n]*?\))?:")
NAMED_AXIOM = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", re.S)
FIXED = {'anchor270_scope/anchor270_source_graph.json': '5ffc7c75e7b71207669bcc8bba8edc89531f047a6e3b709a2de38f77a7729275', 'anchor270_scope/anchor270_source_inventory.json': '239dec03575cb3056401dd7c938232369cecf46d15bdfc7a07584f288d06eac5', 'anchor270_scope/source_tree_identity_bridge.json': '6510e8c6f609bd258bfd3032c8c9d2a51e027b99515d41019dc62d5e8683bd49', 'historical_origin/source_inventory.json': '04fde1d2f971735e254bfcd282e32ea51bd423ff856cab3858efdc4632236284'}
NATIVE_SHA256 = {'run.json': '9027c8a92e69c71c61a5bfc9ab1a0e3fe7f8a3361520684078082d300f8158e9', 'jobs.json': '4a5acd5413979ee760e8844fecde0ef7861006d4d790855d7ddab5724fd96512', 'artifacts.json': 'c8053342720f4b6a0172c418e0837dbbc671c16441d501c3c871b926824da650', 'job.log': 'ded2de40beffd2be9bb5abfc22caa52b9b95a6ddf71b0779cefb89ff767ddbea'}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def file_sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def git_blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()

def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result

def decode(raw):
    def reject_constant(value):
        raise ValueError("Non-finite JSON constant: " + value)
    return json.loads(raw, object_pairs_hook=unique, parse_constant=reject_constant)

def bound(path, digest):
    raw = path.read_bytes()
    require(sha(raw) == digest, "Changed fixed metadata: " + str(path))
    return decode(raw)

def table(rows):
    require(isinstance(rows, (dict, list)), "Invalid module table")
    if isinstance(rows, list):
        names = [r["module"] for r in rows]
        require(len(names) == len(set(names)), "Repeated module row")
        rows = dict(zip(names, rows))
    require(all(n == r["module"] for n, r in rows.items()), "Row/module mismatch")
    return rows

def origin(manifest):
    result = {k: manifest[k] for k in ORIGIN_KEYS}
    if "origin_context" in manifest:
        result["context"] = manifest["origin_context"]
    return result

def expected_named_declarations(code):
    """Resolve only the simple namespace/section syntax in these pinned sources."""
    stack, namespace, result = [], "", []
    for line in code.splitlines():
        line = line.strip()
        match = re.fullmatch(r"namespace\s+([\w.]+)", line)
        if match:
            name = match[1]
            stack.append(("namespace", name, namespace))
            namespace = namespace + "." + name if namespace else name
            continue
        match = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+([\w.]+))?", line)
        if match:
            stack.append(("section", match[1], namespace))
            continue
        match = re.fullmatch(r"end(?:\s+([\w.]+))?", line)
        if match:
            require(bool(stack), "Unmatched source end")
            kind, name, previous = stack.pop()
            require(match[1] is None or match[1] == name, "Unexpected named scope end")
            namespace = previous
            continue
        match = re.fullmatch(r"#print\s+axioms\s+([\w.]+)", line)
        if match:
            name = match[1]
            if name.startswith("_root_."):
                name = name.removeprefix("_root_.")
            elif not name.startswith("Gebendorfer."):
                require(bool(namespace), "Unqualified axiom name outside known namespace")
                name = namespace + "." + name
            result.append(name)
    require(not stack and not namespace, "Unclosed source namespace/section")
    return result

def source_graph(sources, without_comments):
    hashes, deps, closures, active = {}, {}, {}, set()
    for name, raw in sources.items():
        code = without_comments(raw.decode())
        require(not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code, re.M),
                "Forbidden proof escape in " + name)
        require(not re.search(r"^\s*module\s*$", code, re.M), "Unexpected module-system source")
        hashes[name] = sha(raw)
        deps[name] = sorted(set(re.findall(
            r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$", code, re.M)))

    def closure(name):
        if name not in closures:
            require(name in hashes and name not in active, "Missing/cyclic import: " + name)
            active.add(name)
            children = [(dep, closure(dep)) for dep in deps[name]]
            closures[name] = sha(json.dumps([name, hashes[name], PIN, LC, children],
                                           separators=(",", ":")).encode())
            active.remove(name)
        return closures[name]

    closure(ENDPOINT)
    require(set(closures) == set(sources), "Source scope exceeds endpoint closure")
    return dict(source_sha256=hashes, source_dependencies=deps, source_closure_sha256=closures)

def log_payloads(text, prefix=None):
    values = []
    for line in text.splitlines():
        line = re.sub(r"^\d{4}-\d\d-\d\dT\S+\s", "", line)
        line = re.sub(r"\x1b\[[0-9;]*m", "", line)
        if prefix is not None:
            if not line.startswith(prefix):
                continue
            line = line[len(prefix):]
        if line.startswith("{"):
            values.append(decode(line))
    return values

def profiles_from_log(raw, expected):
    text = raw.decode()
    require(not BAD_DIAGNOSTIC.search(text), "Warning/error in completed module log")
    matches = list(NAMED_AXIOM.finditer(text))
    require([m[1] for m in matches] == expected, "Wrong/missing named axiom declaration")
    profiles = [sorted(set(a.strip() for a in (m[2] or "").split(",") if a.strip()))
                for m in matches]
    require(all(set(p) <= ALLOWED for p in profiles), "Nonstandard axiom")
    # verify_extension groups depends-on profiles before axiom-free profiles.
    grouped = [p for m, p in zip(matches, profiles) if m[2] is not None]
    grouped += [p for m, p in zip(matches, profiles) if m[2] is None]
    return grouped, [dict(declaration=m[1], axioms=p) for m, p in zip(matches, profiles)]


def fixed_context():
    fixed = {p: bound(BASE / p, digest) for p, digest in FIXED.items()}
    inventory = fixed['anchor270_scope/anchor270_source_inventory.json']
    reviewed_graph = fixed['anchor270_scope/anchor270_source_graph.json']
    require(inventory['repository'] == REPOSITORY and inventory['commit'] == SOURCE_COMMIT
            and inventory['endpoint'] == ENDPOINT and inventory['mathlib_pin'] == PIN
            and inventory['leancert_pin'] == LC, 'Wrong current source inventory')
    historical = fixed['historical_origin/source_inventory.json']
    require(historical['repository'] == REPOSITORY and historical['commit'] == COMMIT
            and historical['workflow_run'] == RUN and historical['job'] == JOB,
            'Wrong historical workflow inventory')
    files = {}
    for row in historical['files']:
        path = row['path']
        raw = (BASE / 'historical_origin/source' / path).read_bytes()
        require(len(raw) == row['bytes'] and sha(raw) == row['sha256']
                and git_blob(raw) == row['git_blob_sha'], 'Historical source identity: ' + path)
        require(path not in files, 'Duplicate historical source')
        files[path] = raw
    require(len(files) == 21, 'Incomplete historical workflow/helper inventory')
    parser_path = 'Proofs/RG_Lean_20261019/verify.py'
    nodes = [n for n in ast.parse(files[parser_path]).body
             if isinstance(n, ast.FunctionDef) and n.name == 'without_comments']
    require(len(nodes) == 1, 'Missing exact historical comment parser')
    parser_scope = {}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), parser_path, 'exec'), parser_scope)
    without_comments = parser_scope['without_comments']
    sources = {}
    for name, row in inventory['modules'].items():
        rel = 'Proofs/RG_Lean_20261019/' + name.replace('.', '/') + '.lean'
        require(row['path'] == rel, 'Wrong current source path')
        raw = (BASE / 'anchor270_scope/source' / rel).read_bytes()
        require(len(raw) == row['bytes'] and sha(raw) == row['source_sha256']
                and git_blob(raw) == row['git_blob_sha'], 'Current source identity: ' + name)
        sources[name] = raw
    graph = source_graph(sources, without_comments)
    require(len(sources) == 281 and all(reviewed_graph[k] == v for k, v in graph.items()),
            'Current recursive source graph differs')
    require(all(row['source_closure_sha256'] == graph['source_closure_sha256'][name]
                for name, row in inventory['modules'].items()), 'Inventory closure differs')
    require(decode(files[PLAN]) == EXPECTED_PLAN, 'Changed historical restore plan')
    workflow = files[WORKFLOW].decode()
    require('timeout-minutes: 360' in workflow and 'max-parallel: 1' in workflow
            and '--workers 1 --module-timeout 600 --resume' in workflow
            and '--memory-reserve-mib 2048' in workflow
            and 'max_fresh: 163' in workflow and 'assert len(sources)==281' in workflow,
            'Historical resource/source contract differs')
    require(files['lean-toolchain'].decode().strip() == 'leanprover/lean4:v4.33.1',
            'Historical Lean toolchain differs')
    require(decode(files['Proofs/RG_Lean_20261019/ThirdParty/LeanCert/UPSTREAM.json'])['commit'] == LC,
            'Historical LeanCert pin differs')
    lock = decode(files['lake-manifest.json'])
    require([p['rev'] for p in lock['packages'] if p['name'] == 'mathlib'] == [PIN],
            'Historical Mathlib lock differs')
    manifests = {p: decode(files[p]) for p in [BASE_MANIFEST, *EXPECTED_PLAN]}
    expected_priors = {}
    for path, manifest in manifests.items():
        require(manifest['repository'] == REPOSITORY and manifest['mathlib'] == PIN
                and manifest['lean_version'] == '4.33.1', 'Wrong prerequisite pin')
        for name, row in manifest['modules'].items():
            require(name not in expected_priors and row['module'] == name
                    and row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
                    and not row.get('additional_outputs'), 'Invalid historical prerequisite')
            if path == BASE_MANIFEST:
                require(row['mode'] in {'FRESH_KERNEL_EXPORT', 'PRIOR_VERIFIED_JOB_EXPORT'},
                        'Invalid complete base capsule row')
                old_origin = row['origin'] if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT' else origin(manifest)
                expected_priors[name] = dict(row, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=old_origin,
                    transport_capsule={k: manifest[k] for k in ORIGIN_KEYS if k != 'repository'})
            else:
                require(row['mode'] == 'FRESH_KERNEL_EXPORT', 'Prerequisite not originally fresh')
                expected_priors[name] = dict(row, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=origin(manifest))
    priors = set(sources) & set(expected_priors)
    original_fresh = set(sources) - priors
    require(len(expected_priors) == 361 and len(priors) == 118 and len(original_fresh) == 163,
            'Wrong original scope: expected 281 = 118 + 163')
    for name in priors:
        require(expected_priors[name]['source_sha256'] == graph['source_sha256'][name]
                and expected_priors[name]['source_closure_sha256'] == graph['source_closure_sha256'][name],
                'Historical prerequisite differs from current source closure: ' + name)
    names = {n: expected_named_declarations(without_comments(sources[n].decode()))
             for n in original_fresh}
    require(all(names.values()) and sum(map(len, names.values())) == 838,
            'Changed original named declaration scope')
    remaining = {f'Proofs.RadenkovicGutmanWideAnchor270Cell{i:03d}' for i in range(106, 134)}
    remaining |= {f'Proofs.RadenkovicGutmanWideAnchor270Batch{i:03d}' for i in range(10, 14)}
    remaining |= {'Proofs.RadenkovicGutmanWideAnchor270FinitePayment',
                  'Proofs.RadenkovicGutmanWideAnchor270OriginalAnchor', ENDPOINT}
    completed = original_fresh - remaining
    require(remaining <= original_fresh and len(remaining) == 35 and len(completed) == 128
            and sum(len(names[n]) for n in completed) == 655
            and sum(len(names[n]) for n in remaining) == 183, 'Wrong partial frontier')
    return dict(sources=sources, graph=graph, without_comments=without_comments,
                workflow=workflow, expected_priors=expected_priors, prior=priors,
                original_fresh=original_fresh, completed=completed, remaining=remaining,
                names=names, manifest_origins={p: origin(m) for p, m in manifests.items()})


def authenticate(ctx):
    for name, digest in NATIVE_SHA256.items():
        require(file_sha(ACTUAL / name) == digest, 'Changed fixed native capture: ' + name)
    run, jobs, catalog = (decode((ACTUAL / name).read_bytes())
                          for name in ('run.json', 'jobs.json', 'artifacts.json'))
    require(run['id'] == RUN and run['run_attempt'] == ATTEMPT
            and run['repository']['full_name'] == REPOSITORY and run['head_sha'] == COMMIT
            and run['head_branch'] == BRANCH and run['event'] == 'push'
            and run['path'] == WORKFLOW and run['status'] == 'completed'
            and run['conclusion'] == 'cancelled', 'Wrong actual historical run')
    require(jobs['total_count'] == len(jobs['jobs']) == 9
            and len({j['id'] for j in jobs['jobs']}) == 9, 'Incomplete native job catalog')
    selected = [j for j in jobs['jobs'] if j['id'] == JOB]
    require(len(selected) == 1, 'Missing selected historical job')
    job = selected[0]
    require(job['run_id'] == RUN and job['run_attempt'] == ATTEMPT
            and job['head_sha'] == COMMIT and job['head_branch'] == BRANCH
            and job['name'] == JOB_NAME and job['status'] == 'completed'
            and job['conclusion'] == 'cancelled' and job['completed_at'] is not None,
            'Wrong actual historical job')
    steps = {s['name']: s for s in job['steps']}
    require(len(steps) == len(job['steps']) == 14, 'Wrong actual native step catalog')
    require(set(re.findall(r'^      - name: (.+)$', ctx['workflow'].replace('\r\n', '\n'), re.M))
            <= set(steps), 'Missing historical workflow step')
    require(all(s['status'] == 'completed' and s['conclusion'] ==
                ('cancelled' if s['name'] == KERNEL_STEP else 'success') for s in job['steps']),
            'Unexpected native step outcome')
    log = (ACTUAL / 'job.log').read_text()
    require(KERNEL_COMMAND in log and '##[error]The operation was canceled.' in log
            and 'PASS_EXTENSION_SCOPE 281 MODULES; GLOBAL RG NOT_PROVED' not in log,
            'Wrong native kernel invocation or completion observation')
    frontiers = [r for r in log_payloads(log)
                 if r.get('status') == 'EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS']
    expected_frontier = dict(status='EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS',
        endpoint=ENDPOINT, required_modules=281, verified_prior_objects=118, max_fresh=163,
        within_bound=True, proof_status='NOT_PROVEN_BY_RESTORE', complete_submission='NOT_SUBMITTED')
    require(frontiers == [expected_frontier, expected_frontier], 'Wrong native restore/preflight frontier')
    require(log_payloads(log, 'RETAINED_RECORD_COUNTS ') == [dict(total=489, fresh=128)],
            'Wrong native retained record counts')
    logged = table(log_payloads(log, 'COMPLETED_MODULE_JSON '))
    require(set(logged) == ctx['completed'] and all(r['mode'] == 'FRESH_KERNEL_EXPORT'
            for r in logged.values()), 'Wrong actual completed module prefix')
    require(catalog['total_count'] == len(catalog['artifacts']) == 9
            and len({a['id'] for a in catalog['artifacts']}) == 9, 'Incomplete artifact catalog')
    selected = [a for a in catalog['artifacts'] if a['id'] == ARTIFACT_ID]
    require(len(selected) == 1, 'Missing actual producer archive')
    artifact = selected[0]
    require(artifact['name'] == ARTIFACT_NAME and artifact['digest'] == 'sha256:' + ARTIFACT_SHA
            and artifact['size_in_bytes'] == ARTIFACT_BYTES and artifact['expired'] is False,
            'Wrong actual artifact metadata')
    wf = artifact['workflow_run']
    require(wf['id'] == RUN and wf['head_sha'] == COMMIT and wf['head_branch'] == BRANCH
            and wf['repository_id'] == wf['head_repository_id'] == 1416044648,
            'Wrong actual artifact origin')
    path = ACTUAL / 'artifact.zip'
    require(path.stat().st_size == ARTIFACT_BYTES and file_sha(path) == ARTIFACT_SHA,
            'Actual entire ZIP size/digest mismatch')
    audited = {}
    with zipfile.ZipFile(path) as archive:
        members = archive.namelist()
        require(len(members) == len(set(members)) == 668, 'Wrong/duplicate actual ZIP membership')
        for member in members:
            part = pathlib.PurePosixPath(member)
            require(not part.is_absolute() and '..' not in part.parts and '\\' not in member
                    and not archive.getinfo(member).is_dir(), 'Unsafe ZIP member')
        source_paths = {SOURCE_PREFIX + n.replace('.', '/') + '.lean': n for n in ctx['sources']}
        expected_members = set(source_paths) | {SOURCE_MANIFEST, 'diagnostics_records.json',
            'Proofs.RadenkovicGutmanWideAnchor270Cell106.log'}
        for name in ctx['completed']:
            expected_members |= {name + '.json', name + '.log', name.replace('.', '/') + '.olean'}
        require(set(members) == expected_members and 'receipt.json' not in members
                and 'resource_observer.json' not in members, 'Wrong actual partial ZIP scope')
        actual_sources = {n: archive.read(path) for path, n in source_paths.items()}
        require(actual_sources == ctx['sources'], 'Historical/current source bytes differ')
        require(source_graph(actual_sources, ctx['without_comments']) == ctx['graph'],
                'Historical/current recursive source closures differ')
        source_manifest = decode(archive.read(SOURCE_MANIFEST))
        require(source_manifest == dict(endpoint=ENDPOINT, anchor_index=270,
            kind='ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT',
            source_sha256={'Proofs/RG_Lean_20261019/' + n.replace('.', '/') + '.lean': digest
                           for n, digest in ctx['graph']['source_sha256'].items()}),
            'Wrong actual original source manifest')
        diagnostics = table(decode(archive.read('diagnostics_records.json'))['modules'])
        require(set(diagnostics) == set(ctx['expected_priors']) | ctx['completed']
                and len(diagnostics) == 489, 'Wrong actual diagnostic scope')
        for name, expected in ctx['expected_priors'].items():
            require(diagnostics[name] == expected, 'Changed historical prior/origin: ' + name)
        for name in sorted(ctx['completed']):
            row = diagnostics[name]
            require(row == logged[name] == decode(archive.read(name + '.json'))
                    and row['mode'] == 'FRESH_KERNEL_EXPORT' and 'origin' not in row
                    and 'transport_capsule' not in row and not row.get('additional_outputs'),
                    'Wrong fresh record identity/mode: ' + name)
            require(row['source_sha256'] == ctx['graph']['source_sha256'][name]
                    and row['source_closure_sha256'] == ctx['graph']['source_closure_sha256'][name],
                    'Wrong fresh source/closure: ' + name)
            require(type(row['seconds']) in (int, float) and math.isfinite(row['seconds'])
                    and row['seconds'] >= 0, 'Invalid module elapsed time')
            obj = name.replace('.', '/') + '.olean'
            with archive.open(obj) as stream:
                require(hashlib.file_digest(stream, 'sha256').hexdigest() == row['output_sha256'],
                        'Wrong actual object bytes: ' + name)
            module_log = archive.read(name + '.log')
            profiles, named = profiles_from_log(module_log, ctx['names'][name])
            require(profiles == row['axiom_profiles'] and profiles, 'Wrong named axiom profiles')
            audited[name] = dict(row=row, output_bytes=archive.getinfo(obj).file_size,
                                log_sha256=sha(module_log), named_axiom_profiles=named)
        unfinished_log = archive.read('Proofs.RadenkovicGutmanWideAnchor270Cell106.log')
    require(sum(len(r['named_axiom_profiles']) for r in audited.values()) == 655,
            'Wrong total completed named checks')
    observations = log_payloads(log, 'RG_KERNEL_RESOURCE_OBSERVATION ')
    require(observations and not log_payloads(log, 'RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY ')
            and not log_payloads(log, 'RG_KERNEL_RESOURCE_RESULT '),
            'Unexpected/missing partial native observer evidence')
    require(all(type(s['available_bytes']) is int and s['available_bytes'] >= 2048 * 1024**2
                for s in observations if s['lean_processes']), 'Observed reserve violation')
    return dict(status='ACTUAL_CANCELLED_ORIGINAL_ANCHOR270_PARTIAL_EXPORTS_AUTHENTICATED',
        repository=REPOSITORY, run=RUN, job=JOB, run_attempt=ATTEMPT, source_commit=COMMIT,
        current_source_identity_commit=SOURCE_COMMIT, native_run_conclusion='cancelled',
        native_job_conclusion='cancelled', native_job_completed_at=job['completed_at'],
        endpoint=ENDPOINT, authenticator_sha256=file_sha(pathlib.Path(__file__)),
        fixed_input_sha256=FIXED, native_capture_sha256=NATIVE_SHA256,
        artifact={k: artifact[k] for k in ('id', 'name', 'size_in_bytes', 'digest', 'expired')},
        archive_members=668, complete_original_source_bundle_files=281,
        historical_and_current_source_bytes_and_recursive_closures_identical=True,
        endpoint_source_sha256=ctx['graph']['source_sha256'][ENDPOINT],
        endpoint_source_closure_sha256=ctx['graph']['source_closure_sha256'][ENDPOINT],
        required_modules=281, required_historical_prior_modules=118,
        additional_historical_diagnostic_prior_modules=243,
        original_prior_rows_and_origins_preserved=True, preserved_prerequisite_origins=ctx['manifest_origins'],
        completed_fresh_count=128, completed_named_axiom_profiles=655,
        actual_fresh_output_bytes=sum(r['output_bytes'] for r in audited.values()),
        modules=audited, remaining_module_names=sorted(ctx['remaining']),
        remaining_fresh_count=35, remaining_named_axiom_profiles=183,
        unfinished_cell106_log_sha256=sha(unfinished_log),
        resource=dict(native_observation_count=len(observations), archived_final_report_present=False,
            minimum_observed_available_bytes=min(s['available_bytes'] for s in observations),
            maximum_observed_aggregate_lean_rss=max(s['aggregate_lean_rss'] for s in observations),
            module_timeout_seconds=600, workers=1, reserve_mib=2048, job_timeout_minutes=360,
            hidden_intervals_or_completed_observer_claim=False),
        actual_complete_endpoint_receipt_present=False, full_original_endpoint_success_authenticated=False,
        anchor270_certificate_claim=False, degree_one_middle_family_claim=False, global_rg_claim=False,
        family_count_change_from_this_run=0, total_original_families_remaining_after_separate_large_completion=3,
        proof_rows_synthesized=False, production_receipt_created_by_authenticator=False,
        kernel_run_performed_by_authenticator=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-fixed-inputs-only', action='store_true')
    args = parser.parse_args()
    ctx = fixed_context()
    if args.check_fixed_inputs_only:
        print(json.dumps(dict(status='FIXED_ORIGINAL_SOURCE_AND_HISTORICAL_PLAN_VALIDATED_ONLY',
            required_modules=281, historical_prior_modules=118, original_fresh_modules=163,
            expected_completed_prefix_modules=128, expected_remaining_modules=35,
            kernel_run_performed=False, artifact_opened=False)))
        return 0
    target = ACTUAL / 'original_anchor270_partial_authentication.json'
    require(not target.exists(), 'Actual authentication report already exists; do not rerun')
    report = authenticate(ctx)
    raw = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
    pending = target.with_suffix('.json.pending')
    with pending.open('xb') as stream:
        stream.write(raw)
    pending.replace(target)
    print(json.dumps({k: report[k] for k in ('status', 'completed_fresh_count',
        'completed_named_axiom_profiles', 'actual_fresh_output_bytes', 'remaining_fresh_count',
        'full_original_endpoint_success_authenticated', 'anchor270_certificate_claim')}, sort_keys=True))
    print(json.dumps(dict(report=str(target), bytes=len(raw), sha256=sha(raw))))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

