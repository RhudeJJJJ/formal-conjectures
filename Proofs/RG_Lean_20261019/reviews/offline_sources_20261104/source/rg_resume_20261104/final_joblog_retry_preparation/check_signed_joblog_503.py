"""Pure signed-joblog/API opener and clock mocks; no native context or network."""
import ast
import contextlib
import datetime
import email.message
import email.utils
import hashlib
import io
import json
import math
import pathlib
import sys
import types
import unittest.mock
import urllib.error
import urllib.parse
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
COLLECTOR = (ROOT / 'patch/ci/rg_collect_exact_d1_reproductions.py').read_bytes()
API_SOURCE = (ROOT / 'unchanged_dependencies/ci/rg_github_rate_limit.py').read_bytes()
ARTIFACT_SOURCE = (ROOT / 'unchanged_dependencies/ci/rg_github_artifacts.py').read_bytes()
assert hashlib.sha256(API_SOURCE).hexdigest() == '0c5a379458beafada219603bd7b8c1ad3cb8eb276335fa7abd86f04e1132461f'
assert hashlib.sha256(ARTIFACT_SOURCE).hexdigest() == 'db9221ee4aa24f77082c98f33588b987531fc77f9f93c49111d31ad12363b0ef'
JOB = 12345
API_URL = 'https://api.github.com/repos/example/project/actions/jobs/12345/logs'
WALL = datetime.datetime(2026, 11, 4, 19, tzinfo=datetime.timezone.utc).timestamp()
BODY = b'pure fixture job-log bytes, no proof records'
RESULTS = []


class Clock:
    def __init__(self, oversleep=0):
        self.now = 0.0
        self.sleeps = []
        self.oversleep = oversleep

    def monotonic(self):
        return self.now

    def time(self):
        return WALL + self.now

    def sleep(self, seconds):
        assert 0 < seconds <= 30
        self.sleeps.append(seconds)
        self.now += seconds + self.oversleep
        self.oversleep = 0


def target(index):
    return f'https://signed.example.test/joblog/{index}?signature=PRIVATE_SIGNED_TOKEN'


def http_error(code, headers=(), url=API_URL):
    h = email.message.Message()
    for k, v in headers:
        h[k] = v
    return urllib.error.HTTPError(url, code, 'Mock status', h,
        io.BytesIO(b'PRIVATE_RESPONSE_BODY'))


def redirect(index, code=302):
    return http_error(code, [('Location', target(index))])


def service_error(headers=(), code=503):
    return http_error(code, headers, target(0))


class Response:
    def __init__(self, body):
        self.body = body

    def __enter__(self):
        return self

    def __exit__(self, *args):
        pass

    def read(self):
        if isinstance(self.body, BaseException):
            raise self.body
        return self.body


def run(api_actions, signed_actions, clock=None):
    clock = clock or Clock()
    api_calls, signed_calls = [], []
    body_snapshots = []

    def action(actions, index):
        result = actions[index]
        if isinstance(result, tuple):
            result, elapsed = result
            clock.now += elapsed
        if isinstance(result, BaseException):
            raise result
        return result if isinstance(result, Response) else Response(result)

    def api_opener(req, timeout):
        assert isinstance(req, urllib.request.Request) and req.full_url == API_URL
        assert req.get_method() == 'GET' and req.data is None and timeout == 120
        assert req.get_header('Authorization') == 'Bearer PRIVATE_API_TOKEN'
        if api_calls:
            assert req is api_calls[0]
        api_calls.append(req)
        body_snapshots.append((req.full_url, req.data, tuple(req.header_items())))
        return action(api_actions, len(api_calls) - 1)

    def build_opener(handler):
        assert issubclass(handler, urllib.request.HTTPRedirectHandler)
        assert handler().redirect_request(None, None, None, None, None, None) is None
        return types.SimpleNamespace(open=api_opener)

    def signed_opener(url, timeout):
        # Only a URL string and timeout are accepted, never API credentials.
        assert type(url) is str and timeout == 120
        signed_calls.append(url)
        return action(signed_actions, len(signed_calls) - 1)

    api_module = types.ModuleType('pure_current_api_helper')
    exec(compile(API_SOURCE, '<fixed-api-helper>', 'exec'), api_module.__dict__)
    api_module.time = clock
    artifact_module = types.ModuleType('rg_github_artifacts')
    artifact_module.__dict__.update(email=email, math=math, time=clock)
    parser = next(n for n in ast.parse(ARTIFACT_SOURCE).body if isinstance(n, ast.FunctionDef)
                  and n.name == '_service_retry_delay')
    exec(compile(ast.Module(body=[parser], type_ignores=[]), '<fixed-pure-service-parser>', 'exec'),
         artifact_module.__dict__)
    request_namespace = types.SimpleNamespace(Request=urllib.request.Request,
        HTTPRedirectHandler=urllib.request.HTTPRedirectHandler,
        build_opener=build_opener, urlopen=signed_opener)
    namespace = dict(urllib=types.SimpleNamespace(error=urllib.error, parse=urllib.parse,
        request=request_namespace), api_open=api_module.api_open, time=clock, json=json)
    node = next(n for n in ast.parse(COLLECTOR).body if isinstance(n, ast.ClassDef) and n.name == 'GitHub')
    exec(compile(ast.Module(body=[node], type_ignores=[]), '<collector-class-only>', 'exec'), namespace)
    client = namespace['GitHub'].__new__(namespace['GitHub'])
    client.base = 'https://api.github.com/repos/example/project'
    client.headers = {'Authorization': 'Bearer PRIVATE_API_TOKEN', 'Accept': 'application/vnd.github+json'}
    stdout = io.StringIO()
    result = caught = None
    with unittest.mock.patch.dict(sys.modules, {'rg_github_artifacts': artifact_module}):
        with contextlib.redirect_stdout(stdout):
            try:
                result = client.logs(JOB)
            except BaseException as exc:
                caught = exc
    assert not body_snapshots or all(s == body_snapshots[0] for s in body_snapshots)
    events = [json.loads(line) for line in stdout.getvalue().splitlines()]
    joblog_events = [e for e in events if e['status'].startswith(('SIGNED_JOBLOG_', 'WAITING_FOR_SIGNED_JOBLOG_'))]
    encoded = json.dumps(joblog_events)
    assert all(secret not in encoded for secret in ('PRIVATE_API_TOKEN', 'PRIVATE_SIGNED_TOKEN', 'PRIVATE_RESPONSE_BODY', 'https://'))
    assert all(e['job'] == JOB for e in joblog_events)
    return dict(result=result, error=caught, api_calls=api_calls, signed_calls=signed_calls,
                clock=clock, events=events, joblog_events=joblog_events)


def case(name, check):
    try:
        check()
        RESULTS.append(dict(name=name, status='PASS'))
    except BaseException as exc:
        RESULTS.append(dict(name=name, status='FAIL', error_type=type(exc).__name__, detail=str(exc)))


def retry_success(headers=(), delay=30):
    r = run([redirect(1), redirect(2)], [service_error(headers), BODY])
    assert r['result'] == BODY and r['error'] is None
    assert len(r['api_calls']) == 2 and r['signed_calls'] == [target(1), target(2)]
    assert sum(r['clock'].sleeps) == delay
    assert r['joblog_events'][0]['decision'] == 'RETRY_SAME_JOB_WITH_FRESH_REDIRECT_AFTER_WAIT'


def stopped(api, downloads, api_count, signed_count, decision=None, clock=None):
    r = run(api, downloads, clock=clock)
    assert isinstance(r['error'], urllib.error.HTTPError) and r['error'].code == 503
    assert r['result'] is None and len(r['api_calls']) == api_count and len(r['signed_calls']) == signed_count
    if decision:
        assert r['joblog_events'][-1]['decision'] == decision
    return r


def exhausted():
    r = stopped([redirect(i) for i in range(4)], [service_error() for _ in range(4)], 4, 4, 'STOP_ATTEMPTS_EXHAUSTED')
    assert sum(r['clock'].sleeps) == 210
    assert [e['wait_seconds'] for e in r['joblog_events'] if 'wait_seconds' in e] == [30, 60, 120]


case('signed_503_success_same_job_new_redirect_and_token_confinement', retry_success)
case('four_signed_GET_limit_backoffs_30_60_120', exhausted)
case('standard_retry_seconds', lambda: retry_success([('Retry-After', '90')], 90))
future = email.utils.format_datetime(datetime.datetime.fromtimestamp(WALL + 75, datetime.timezone.utc), usegmt=True)
case('standard_retry_HTTP_date', lambda: retry_success([('Retry-After', future)], 75))
case('documented_service_milliseconds_and_maximum', lambda: retry_success([('Retry-After', '45'), ('retry-after-ms', '70000'), ('x-ms-retry-after-ms', '90000')], 90))
case('shorter_service_wait_does_not_reduce_backoff', lambda: retry_success([('Retry-After', '1')], 30))
for label, headers in [('empty', [('Retry-After', '')]), ('invalid_date', [('Retry-After', 'not-a-date')]),
    ('timezone_missing', [('Retry-After', 'Wed, 04 Nov 2026 19:01:15')]),
    ('invalid_ms', [('x-ms-retry-after-ms', '1.5')])]:
    case('invalid_explicit_header_' + label, lambda headers=headers: stopped([redirect(1)], [service_error(headers)], 1, 1, 'STOP_INVALID_SERVICE_RETRY_HEADER'))
case('too_long_explicit_wait_fails_closed', lambda: stopped([redirect(1)], [service_error([('Retry-After', '601')])], 1, 1, 'STOP_SERVICE_WAIT_EXCEEDS_RETRY_WINDOW'))
case('initial_elapsed_window_includes_API_and_download', lambda: stopped([redirect(1)], [(service_error(), 580)], 1, 1, 'STOP_SERVICE_WAIT_EXCEEDS_RETRY_WINDOW'))
case('oversleep_stops_before_new_API_request', lambda: stopped([redirect(1)], [service_error()], 1, 1, 'STOP_RETRY_START_WINDOW_AFTER_WAIT', Clock(oversleep=600)))
case('API_rate_wait_during_fresh_redirect_stops_new_signed_GET', lambda: stopped(
    [redirect(1), http_error(429, [('Retry-After', '600')]), redirect(2)], [service_error()], 3, 1, 'STOP_RETRY_WINDOW_DURING_REDIRECT'))


def inline(after_retry=False):
    r = run([redirect(1), BODY] if after_retry else [BODY], [service_error()] if after_retry else [])
    assert r['result'] == BODY and r['error'] is None and len(r['signed_calls']) == int(after_retry)


case('existing_inline_API_200_path', inline)
case('fresh_same_job_API_200_after_signed_503', lambda: inline(True))
for code in [301, 302, 303, 307, 308]:
    def redirect_case(code=code):
        r = run([redirect(1, code)], [BODY])
        assert r['result'] == BODY and r['error'] is None and r['clock'].sleeps == []
    case('existing_redirect_' + str(code), redirect_case)
for code in [401, 403, 429, 500, 502, 504]:
    def no_signed_retry(code=code):
        err = service_error(code=code)
        r = run([redirect(1)], [err])
        assert r['error'] is err and len(r['api_calls']) == len(r['signed_calls']) == 1
        assert r['clock'].sleeps == [] and r['joblog_events'] == []
    case('signed_HTTP_' + str(code) + '_not_retried', no_signed_retry)
for name, err in [('transport', urllib.error.URLError('pure mock')), ('timeout', TimeoutError('pure mock'))]:
    def no_transport_retry(err=err):
        r = run([redirect(1)], [err])
        assert r['error'] is err and len(r['api_calls']) == len(r['signed_calls']) == 1
        assert r['clock'].sleeps == [] and r['joblog_events'] == []
    case(name + '_not_retried', no_transport_retry)


def api_503_not_signed_retry():
    r = run([http_error(503)], [])
    assert isinstance(r['error'], AssertionError) and len(r['api_calls']) == 1
    assert not r['signed_calls'] and not r['joblog_events'] and not r['clock'].sleeps


case('API_503_keeps_existing_nonredirect_failure', api_503_not_signed_retry)
for code, delay in [(403, 3), (429, 3), (502, 30)]:
    def old_api_path(code=code, delay=delay):
        r = run([http_error(code, [('Retry-After', '2')]), redirect(1)], [BODY])
        assert r['result'] == BODY and r['error'] is None and len(r['api_calls']) == 2
        assert len(r['signed_calls']) == 1 and sum(r['clock'].sleeps) == delay and not r['joblog_events']
    case('existing_API_' + str(code) + '_handling_unchanged', old_api_path)
for label, location in [('http', 'http://signed.example.test/log'), ('userinfo', 'https://user:secret@signed.example.test/log')]:
    def wrong_location(location=location):
        r = run([http_error(302, [('Location', location)])], [])
        assert isinstance(r['error'], AssertionError) and not r['signed_calls']
    case('existing_redirect_safety_' + label, wrong_location)

old = (ROOT / 'base/ci/rg_collect_exact_d1_reproductions.py').read_bytes()
old_tree, new_tree = ast.parse(old), ast.parse(COLLECTOR)
old_class = next(n for n in old_tree.body if isinstance(n, ast.ClassDef) and n.name == 'GitHub')
new_class = next(n for n in new_tree.body if isinstance(n, ast.ClassDef) and n.name == 'GitHub')
old_method = next(n for n in old_class.body if isinstance(n, ast.FunctionDef) and n.name == 'logs')
new_method = next(n for n in new_class.body if isinstance(n, ast.FunctionDef) and n.name == 'logs')
new_class.body[new_class.body.index(new_method)] = old_method
assert ast.dump(old_tree, include_attributes=False) == ast.dump(new_tree, include_attributes=False)
old_lines, new_lines = old.splitlines(keepends=True), COLLECTOR.splitlines(keepends=True)
assert old_lines[:old_method.lineno - 1] == new_lines[:new_method.lineno - 1]
assert old_lines[old_method.end_lineno:] == new_lines[new_method.end_lineno:]
oldw = (ROOT / 'base/.github/workflows/rg-degree-one-large-join-repair-20261104.yml').read_bytes()
neww = (ROOT / 'patch/.github/workflows/rg-degree-one-large-join-repair-20261104.yml').read_bytes()
assert neww.replace(b"      - 'ci/rg_collect_exact_d1_reproductions.py'\n", b'', 1) == oldw
report = dict(status='PASS' if all(r['status'] == 'PASS' for r in RESULTS) else 'FAIL',
    cases=RESULTS, case_count=len(RESULTS), collector_sha256=hashlib.sha256(COLLECTOR).hexdigest(),
    unchanged_API_helper_sha256=hashlib.sha256(API_SOURCE).hexdigest(),
    reused_pure_service_parser_source_sha256=hashlib.sha256(ARTIFACT_SOURCE).hexdigest(),
    workflow_sha256=hashlib.sha256(neww).hexdigest(),
    exact_collector_bytes_outside_GitHub_logs_unchanged=True,
    AST_reverts_to_exact_base_by_replacing_only_GitHub_logs=True,
    workflow_only_adds_collector_push_path=True, network_requests=0, real_sleeps=0,
    native_or_GHA_environment_simulated=False, ZIP_reads=False, proof_or_full_authenticator_executed=False,
    executed_scope='Only isolated GitHub class, existing API helper and frozen pure service-wait parser with injected opener/clock stubs; no collector main or constructor.')
raw = (json.dumps(report, indent=2) + '\n').encode()
(ROOT / 'focused_mock_validation.json').write_bytes(raw)
print(json.dumps({'status':report['status'],'cases':len(RESULTS),
    'failures':[r for r in RESULTS if r['status'] != 'PASS'],
    'report_bytes':len(raw),'report_sha256':hashlib.sha256(raw).hexdigest()}))
raise SystemExit(0 if report['status'] == 'PASS' else 1)
