"""Bounded diagnostic for the unchanged EscapeReducedReserve source.

Default: original bytes with the strict verifier's supported --profile CLI.
An explicitly selected runner-only marker copy can localize declaration
boundaries if ordinary profiler output is inconclusive. Neither mode exports
proof objects or a reusable proof receipt. Original declaration text is kept
verbatim; the checked-out source is restored in a finally block.
"""
import argparse, hashlib, json, pathlib, re, shutil, subprocess, sys
from rg_plan_exact_degree_one_large import source_closure

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
BUILD = SOURCES / 'build/extension'
OUT = SOURCES / 'build/escape_diagnostics'
ENDPOINT = 'Proofs.RadenkovicGutmanEscapeReducedReserve'
SOURCE = SOURCES / (ENDPOINT.replace('.', '/') + '.lean')
SOURCE_SHA = 'cafecd99d1755286e6fe6d5b31614e993502a2d63eecb1ce6df1d8cb2f1a05e2'
CLOSURE_SHA = 'ead5d4e142f01dade7208ff766d232e8fab6cd08b1f09e683f23c2f5db051c0e'
PREFIX = 'RG_ESCAPE_DIAGNOSTIC_'


def sha(raw): return hashlib.sha256(raw).hexdigest()


def prepare_markers(raw):
    text = raw.decode()
    rules = [
        ('noncomputable def data :', 'BEFORE_DATA'),
        ('theorem accepted :', 'BEFORE_ACCEPTED'),
        ('theorem unit_box_nonneg ', 'AFTER_ACCEPTED_BEFORE_UNIT_BOX'),
        ('theorem data_eval ', 'AFTER_UNIT_BOX_BEFORE_DATA_EVAL'),
        ('#print axioms accepted', 'AFTER_DATA_EVAL'),
    ]
    inserted = []
    lines = text.splitlines(keepends=True)
    result = []
    for line in lines:
        for start, label in rules:
            if line.startswith(start):
                marker = '#eval IO.eprintln "' + PREFIX + label + '"\n'
                inserted.append(marker)
                result.append(marker)
        result.append(line)
    assert len(inserted) == len(rules)
    rendered = ''.join(result).encode()
    stripped = rendered.decode()
    for marker in inserted:
        assert stripped.count(marker) == 1
        stripped = stripped.replace(marker, '')
    assert stripped.encode() == raw, 'Instrumentation changed an original declaration'
    return rendered


def collect():
    OUT.mkdir(parents=True, exist_ok=True)
    log = BUILD / (ENDPOINT + '.log')
    text = log.read_text() if log.is_file() else ''
    if log.is_file(): shutil.copyfile(log, OUT / 'original_module_profiler.log')
    resource = SOURCES / 'build/fresh_exports/resource_observer.json'
    if resource.is_file(): shutil.copyfile(resource, OUT / 'resource_observer.json')
    markers = re.findall(r'RG_ESCAPE_DIAGNOSTIC_[A-Z_]+', text)
    timings = [line for line in text.splitlines() if ' took ' in line]
    report = {
        'kind': 'ESCAPE_ORIGINAL_SOURCE_DIAGNOSTIC_ONLY',
        'source_sha256_after_cleanup': sha(SOURCE.read_bytes()),
        'source_restored': sha(SOURCE.read_bytes()) == SOURCE_SHA,
        'observed_markers': markers,
        'last_completed_boundary_marker': markers[-1] if markers else None,
        'completed_profiler_timing_lines': len(timings),
        'last_profiler_timings': timings[-40:],
        'interpretation': 'Profiler timing lines describe completed components; missing lines do not prove which declaration was active. Runner-copy boundary markers, when explicitly enabled, are emitted between sequential original commands.',
        'proof_receipt': 'NOT_EXPORTED_OR_REUSABLE',
        'original_theorem_scope': 'UNCHANGED_IN_ORIGINAL_BYTES_MODE; VERBATIM_DECLARATIONS_IN_RUNNER_MARKER_MODE',
    }
    (OUT / 'diagnostic_summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--phase', choices=('preflight', 'run', 'collect'), required=True)
    p.add_argument('--instrument-runner-copy', action='store_true')
    a = p.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    if a.phase == 'collect':
        collect()
        return
    original = SOURCE.read_bytes()
    assert sha(original) == SOURCE_SHA
    hashes, _, closures = source_closure(ENDPOINT)
    assert len(hashes) == 12 and closures[ENDPOINT] == CLOSURE_SHA
    if a.phase == 'preflight':
        subprocess.run([sys.executable, '-B', 'ci/rg_restore_with_kernel_fallback.py',
            '--plan', 'ci/rg_empty_restore_plan.json', '--build-directory', str(BUILD),
            '--endpoint', ENDPOINT, '--max-fresh', '1', '--preflight-only'], cwd=ROOT, check=True)
        frontier = json.loads((BUILD / 'bounded_kernel_fallback_plan.json').read_bytes())
        assert frontier['required_modules'] == 12 and frontier['fresh_modules'] == [ENDPOINT]
        shutil.copyfile(BUILD / 'bounded_kernel_fallback_plan.json', OUT / 'exact_original_frontier.json')
        return
    actual = prepare_markers(original) if a.instrument_runner_copy else original
    (OUT / 'source_identity.json').write_text(json.dumps({
        'kind': 'DIAGNOSTIC_SOURCE_IDENTITY', 'original_sha256': SOURCE_SHA,
        'original_closure_sha256': CLOSURE_SHA, 'diagnostic_sha256': sha(actual),
        'mode': 'RUNNER_ONLY_BOUNDARY_MARKERS' if a.instrument_runner_copy else 'ORIGINAL_BYTES_WITH_CLI_PROFILER',
        'original_declarations_verbatim': True, 'kernel_flags_preserved': True,
        'profiling_cli': '--profile', 'module_timeout': 1200,
        'workers': 1, 'memory_reserve_mib': 2048, 'reusable_proof_receipt': False,
    }, indent=2) + '\n')
    if a.instrument_runner_copy:
        (OUT / 'runner_only_instrumented_source.lean').write_bytes(actual)
    try:
        SOURCE.write_bytes(actual)
        result = subprocess.run([sys.executable, '-B', 'ci/rg_observed_kernel_verify.py',
            '--memory-reserve-mib', '2048', '--', '--mathlib-project', str(ROOT),
            '--endpoint', ENDPOINT, '--workers', '1', '--module-timeout', '1200',
            '--resume', '--profile'], cwd=ROOT)
    finally:
        SOURCE.write_bytes(original)
        assert sha(SOURCE.read_bytes()) == SOURCE_SHA
        collect()
    raise SystemExit(result.returncode)


if __name__ == '__main__': main()
