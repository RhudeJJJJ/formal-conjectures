"""Pure HTTPError/opener/clock mocks; no network, real sleeps, or GH context."""
import ast
import contextlib
import datetime
import email.message
import email.utils
import hashlib
import io
import json
import pathlib
import types
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
OLD = (ROOT / 'base/ci/rg_github_rate_limit.py').read_bytes()
NEW = (ROOT / 'patch/ci/rg_github_rate_limit.py').read_bytes()
WALL = datetime.datetime(2026, 11, 4, 18, tzinfo=datetime.timezone.utc).timestamp()
SUCCESS = object()
RESULTS = []


class Clock:
    def __init__(self, oversleep=0, jumps=None):
        self.now = 0.0
        self.sleeps = []
        self.oversleep = oversleep
        self.jumps = jumps or {}
        self.calls = 0

    def monotonic(self):
        self.calls += 1
        self.now = self.jumps.get(self.calls, self.now)
        return self.now

    def time(self):
        return WALL + self.now

    def sleep(self, seconds):
        assert 0 < seconds <= 30
        self.sleeps.append(seconds)
        self.now += seconds + self.oversleep
        self.oversleep = 0


def request(url='https://api.github.com/repos/owner/repo/actions/runs/1/jobs', method='GET', data=None):
    return urllib.request.Request(url, data=data, method=method,
        headers={'Authorization': 'Bearer PRIVATE_TEST_MARKER'})


def error(code=502, headers=(), body='PRIVATE_RESPONSE_MARKER', url=None):
    h = email.message.Message()
    for k, v in headers:
        h[k] = v
    return urllib.error.HTTPError(url or request().full_url, code, 'Mock status', h,
        io.BytesIO(body.encode()))


def run(source, actions, req=None, clock=None):
    req = request() if req is None else req
    clock = clock or Clock()
    module = types.ModuleType('isolated_pure_api_mock')
    exec(compile(source, '<read-only-helper-bytes>', 'exec'), module.__dict__)
    module.time = clock
    calls = []
    before = (req.full_url, req.get_method(), req.data, req.header_items(),
              dict(req.unredirected_hdrs)) if isinstance(req, urllib.request.Request) else req

    def opener(actual, timeout):
        assert actual is req and timeout == 120
        calls.append((id(actual), timeout))
        action = actions[len(calls) - 1]
        if isinstance(action, tuple):
            action, advance = action
            clock.now += advance
        if isinstance(action, BaseException):
            raise action
        return action

    output = io.StringIO()
    result = caught = None
    with contextlib.redirect_stdout(output):
        try:
            result = module.api_open(req, opener=opener)
        except BaseException as exc:
            caught = exc
    after = (req.full_url, req.get_method(), req.data, req.header_items(),
             dict(req.unredirected_hdrs)) if isinstance(req, urllib.request.Request) else req
    assert before == after
    return dict(result=result, error=caught, calls=calls, clock=clock,
                output=output.getvalue(), events=[json.loads(s) for s in output.getvalue().splitlines()])


def case(name, function):
    try:
        function()
        RESULTS.append(dict(name=name, status='PASS'))
    except BaseException as exc:
        RESULTS.append(dict(name=name, status='FAIL', error_type=type(exc).__name__, detail=str(exc)))


def successful_retry(headers=(), delay=30, req=None):
    e = error(headers=headers)
    r = run(NEW, [e, SUCCESS], req=req)
    assert r['result'] is SUCCESS and r['error'] is None and len(r['calls']) == 2
    assert sum(r['clock'].sleeps) == delay
    assert e.fp.closed
    assert all(s not in r['output'] for s in ('PRIVATE_TEST_MARKER', 'PRIVATE_RESPONSE_MARKER', 'https://', 'api.github.com'))
    assert r['events'][0]['decision'] == 'RETRY_IDENTICAL_GET_AFTER_WAIT'
    assert all(e['no_request_during_wait'] for e in r['events'][1:])


def stopped(actions, count=1, req=None, clock=None, decision=None):
    r = run(NEW, actions, req=req, clock=clock)
    assert isinstance(r['error'], urllib.error.HTTPError) and len(r['calls']) == count
    assert r['result'] is None
    if decision:
        assert r['events'][-1]['decision'] == decision
    return r


def four_attempts():
    es = [error() for _ in range(4)]
    r = stopped(es, count=4, decision='STOP_ATTEMPTS_EXHAUSTED')
    assert r['error'] is es[-1] and sum(r['clock'].sleeps) == 210
    assert [e['wait_seconds'] for e in r['events'] if 'wait_seconds' in e] == [30, 60, 120]


def parity(factory, req=None):
    a, b = run(OLD, factory(), req=req), run(NEW, factory(), req=req)
    signature = lambda r: (r['result'] is SUCCESS, type(r['error']).__name__,
        getattr(r['error'], 'code', None), len(r['calls']), r['clock'].sleeps, r['output'])
    assert signature(a) == signature(b)


case('actual_HTTPError_502_then_success_same_request_and_private_logs', successful_retry)
case('exact_four_shared_attempts_backoffs_30_60_120', four_attempts)
case('elapsed_window_before_wait_stops', lambda: stopped([(error(), 600)], decision='STOP_WAIT_EXCEEDS_RETRY_START_WINDOW'))
case('oversleep_rechecked_after_wait', lambda: stopped([error()], clock=Clock(oversleep=600), decision='STOP_RETRY_WINDOW_AFTER_WAIT'))
case('window_rechecked_immediately_before_retry', lambda: stopped([error()], clock=Clock(jumps={8: 600}), decision='STOP_RETRY_WINDOW_BEFORE_REQUEST'))
case('integer_Retry_After_respected', lambda: successful_retry([('Retry-After', '90')], 90))
case('backoff_is_minimum_not_shortened_by_header', lambda: successful_retry([('Retry-After', '5')], 30))
future = datetime.datetime.fromtimestamp(WALL + 75, datetime.timezone.utc)
case('IMF_HTTP_date_respected', lambda: successful_retry([('Retry-After', email.utils.format_datetime(future, usegmt=True))], 75))
case('obsolete_RFC850_HTTP_date_respected', lambda: successful_retry([('Retry-After', future.strftime('%A, %d-%b-%y %H:%M:%S GMT'))], 75))
case('obsolete_asctime_HTTP_date_respected', lambda: successful_retry([('Retry-After', future.strftime('%a %b %e %H:%M:%S %Y'))], 75))
past = datetime.datetime.fromtimestamp(WALL - 10, datetime.timezone.utc)
case('past_valid_date_preserves_minimum_backoff', lambda: successful_retry([('Retry-After', email.utils.format_datetime(past, usegmt=True))], 30))
for label, value in [('empty', ''), ('garbage', 'bad-date'), ('negative', '-1'), ('decimal', '1.5'),
    ('no_timezone', 'Wed, 04 Nov 2026 18:01:15'), ('trailing_junk', 'Wed, 04 Nov 2026 18:01:15 GMT junk'),
    ('overlong', '9' * 129), ('invalid_calendar', 'Wed, 31 Feb 2026 18:01:15 GMT')]:
    case('invalid_Retry_After_' + label, lambda value=value: stopped([error(headers=[('Retry-After', value)])], decision='STOP_INVALID_RETRY_AFTER'))
case('repeated_Retry_After_rejected', lambda: stopped([error(headers=[('Retry-After', '30'), ('Retry-After', '60')])], decision='STOP_INVALID_RETRY_AFTER'))
case('explicit_wait_outside_600s_window_rejected', lambda: stopped([error(headers=[('Retry-After', '601')])], decision='STOP_WAIT_EXCEEDS_RETRY_START_WINDOW'))
case('exact_600s_start_boundary_rejected', lambda: stopped([error(headers=[('Retry-After', '600')])], decision='STOP_WAIT_EXCEEDS_RETRY_START_WINDOW'))
for label, req in [('URL_string', request().full_url), ('http', request('http://api.github.com/x')),
    ('foreign_host', request('https://example.test/x')), ('host_suffix', request('https://api.github.com.example.test/x')),
    ('userinfo', request('https://owner@api.github.com/x')), ('explicit_port', request('https://api.github.com:443/x')),
    ('POST', request(method='POST')), ('HEAD', request(method='HEAD')), ('GET_with_empty_data', request(data=b''))]:
    case('ineligible_request_' + label, lambda req=req: stopped([error()], req=req, decision='STOP_OUTSIDE_EXACT_GET_SCOPE'))
case('foreign_response_origin_not_retried', lambda: stopped([error(url='https://example.test/x')], decision='STOP_OUTSIDE_EXACT_GET_SCOPE'))
for code in [500, 503, 401, 404]:
    case('other_HTTP_' + str(code) + '_unchanged', lambda code=code: parity(lambda: [error(code, [('Retry-After', '1')], 'neutral')]))
for code in [301, 302, 303, 307, 308]:
    case('redirect_' + str(code) + '_unchanged', lambda code=code: parity(lambda: [error(code, [('Location', 'https://example.test/object')])]))
for code in [403, 429]:
    case('legacy_' + str(code) + '_seconds', lambda code=code: parity(lambda: [error(code, [('Retry-After', '2')], '{}'), SUCCESS]))
    case('legacy_' + str(code) + '_reset', lambda code=code: parity(lambda: [error(code, [('x-ratelimit-remaining', '0'), ('x-ratelimit-reset', str(int(WALL) + 10))], '{}'), SUCCESS]))
    case('legacy_' + str(code) + '_secondary', lambda code=code: parity(lambda: [error(code, body='{"message":"secondary rate limit"}'), SUCCESS]))
    case('legacy_' + str(code) + '_not_rate_limited', lambda code=code: parity(lambda: [error(code, body='{"message":"permission failure"}')]))
    case('legacy_' + str(code) + '_3700s_boundary', lambda code=code: parity(lambda: [error(code, [('Retry-After', '3699')], '{}'), SUCCESS]))
    case('legacy_' + str(code) + '_over_3700s', lambda code=code: parity(lambda: [error(code, [('Retry-After', '3700')], '{}')]))
case('legacy_shared_four_attempts', lambda: parity(lambda: [error(429, [('Retry-After', '1')], '{}') for _ in range(4)]))


def transport_untouched(exc):
    r = run(NEW, [exc])
    assert r['error'] is exc and len(r['calls']) == 1 and r['clock'].sleeps == []


for name, exc in [('URL_error', urllib.error.URLError('mock transport failure')),
                  ('timeout', TimeoutError('mock timeout')), ('hash_assertion', AssertionError('mock hash failure'))]:
    case(name + '_not_retried', lambda exc=exc: transport_untouched(exc))


def mixed_legacy_wait():
    r = run(NEW, [error(), error(429, [('Retry-After', '700')], '{}'), SUCCESS])
    assert r['result'] is SUCCESS and len(r['calls']) == 3 and r['clock'].now == 731


def shared_counter_mixed():
    r = stopped([error(429, [('Retry-After', '1')], '{}'), error(), error(), error()], count=4, decision='STOP_ATTEMPTS_EXHAUSTED')
    assert [e['wait_seconds'] for e in r['events'] if 'wait_seconds' in e] == [60, 120]


case('old_429_wait_after_502_is_not_capped_by_new_window', mixed_legacy_wait)
case('502_and_429_share_the_original_four_attempt_counter', shared_counter_mixed)

ast.parse(OLD)
ast.parse(NEW)
old_legacy = OLD[OLD.index(b"            body = error.read(4096)"):]
new_legacy = NEW[NEW.index(b"            body = error.read(4096)"):]
assert old_legacy == new_legacy
old_redirect = b'            if error.code in (301, 302, 303, 307, 308): raise\n'
assert OLD.count(old_redirect) == NEW.count(old_redirect) == 1
old_workflow = (ROOT / 'base/.github/workflows/rg-degree-one-large-join-repair-20261104.yml').read_bytes()
new_workflow = (ROOT / 'patch/.github/workflows/rg-degree-one-large-join-repair-20261104.yml').read_bytes()
assert new_workflow.replace(b"      - 'ci/rg_github_rate_limit.py'\n", b'', 1) == old_workflow
report = dict(status='PASS' if all(r['status'] == 'PASS' for r in RESULTS) else 'FAIL',
    helper_sha256=hashlib.sha256(NEW).hexdigest(), base_helper_sha256=hashlib.sha256(OLD).hexdigest(),
    workflow_sha256=hashlib.sha256(new_workflow).hexdigest(), case_count=len(RESULTS), cases=RESULTS,
    legacy_403_429_error_body_and_3700s_block_byte_identical=True, redirects_byte_identical=True,
    workflow_only_added_push_path=True, syntax='ast.parse',
    executed_scope='Pure mock opener, fake clock and real urllib HTTPError/Request objects only.',
    network_requests=0, real_sleeps=0, native_context_simulation=False, github_environment_simulation=False,
    proof_or_actual_authenticator_executed=False)
raw = (json.dumps(report, indent=2) + '\n').encode()
(ROOT / 'focused_mock_validation.json').write_bytes(raw)
print(json.dumps({'status':report['status'], 'cases':len(RESULTS), 'failures':[r for r in RESULTS if r['status'] != 'PASS'],
                  'report_bytes':len(raw), 'report_sha256':hashlib.sha256(raw).hexdigest()}))
raise SystemExit(0 if report['status'] == 'PASS' else 1)
