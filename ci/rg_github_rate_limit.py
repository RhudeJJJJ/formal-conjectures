"""Respect explicit GitHub API rate limits without retrying permission failures."""
import json, time, urllib.error, urllib.request
import datetime, email.utils, math, re, urllib.parse


def _exact_github_api_get(request, error):
    """Never extend retries to URL strings, uploads, or another origin."""
    if not isinstance(request, urllib.request.Request): return False
    if request.get_method() != 'GET' or request.data is not None: return False
    try:
        origins = [urllib.parse.urlsplit(url) for url in (request.full_url, error.geturl())]
    except (TypeError, ValueError):
        return False
    return all(url.scheme == 'https' and url.netloc == 'api.github.com' for url in origins)


def _api_502_retry_after(headers):
    """Read only standard Retry-After; invalid explicit values stop retries."""
    raw = headers.get('Retry-After')
    if raw is None: return 0.0
    if hasattr(headers, 'get_all') and len(headers.get_all('Retry-After')) != 1:
        raise ValueError('Repeated API Retry-After header')
    if not isinstance(raw, str): raise ValueError('Invalid API Retry-After header')
    value = raw.strip(' \t')
    if not value or len(value) > 128: raise ValueError('Invalid API Retry-After header')
    if value.isascii() and value.isdigit():
        seconds = float(int(value))
    else:
        weekday = r'(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun)'
        month = r'(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)'
        clock = r'[0-9]{2}:[0-9]{2}:[0-9]{2}'
        imf = re.fullmatch(weekday + ', [0-9]{2} ' + month + r' [0-9]{4} ' + clock + ' GMT', value)
        rfc850 = re.fullmatch(r'(?:Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday), '
            + '[0-9]{2}-' + month + r'-([0-9]{2}) ' + clock + ' GMT', value)
        asctime = re.fullmatch(weekday + ' ' + month + r' (?: [0-9]|[0-9]{2}) '
            + clock + r' [0-9]{4}', value)
        if not (imf or rfc850 or asctime): raise ValueError('Invalid HTTP retry date')
        date = email.utils.parsedate_to_datetime(value)
        if date.tzinfo is None:
            if not asctime: raise ValueError('API retry date has no timezone')
            date = date.replace(tzinfo=datetime.timezone.utc)
        now = time.time()
        if rfc850:
            current = datetime.datetime.fromtimestamp(now, datetime.timezone.utc)
            year = (current.year // 100) * 100 + int(rfc850.group(1))
            date = date.replace(year=year)
            if (date.year, date.month, date.day, date.hour, date.minute, date.second) > (
                current.year + 50, current.month, current.day, current.hour, current.minute, current.second):
                date = date.replace(year=year - 100)
        seconds = max(0.0, date.timestamp() - now)
    if not math.isfinite(seconds): raise ValueError('Nonfinite API retry delay')
    return seconds


def api_open(request, opener=None):
    if opener is None: opener = urllib.request.urlopen
    started = time.monotonic()
    retry_502_error = None
    for attempt in range(4):
        if retry_502_error is not None:
            if time.monotonic() - started >= 600:
                print(json.dumps(dict(status='GITHUB_EXACT_PROOF_API_HTTP_502',
                    decision='STOP_RETRY_WINDOW_BEFORE_REQUEST', previous_error_attempt=attempt,
                    next_attempt=attempt + 1, retry_start_window_seconds=600)), flush=True)
                raise retry_502_error
            retry_502_error = None
        try:
            return opener(request, timeout=120)
        except urllib.error.HTTPError as error:
            if error.code in (301, 302, 303, 307, 308): raise
            if error.code == 502:
                # The 600-second bound controls new 502 retry starts, not an
                # in-flight 120-second call or the unchanged 403/429 handling.
                event = dict(status='GITHUB_EXACT_PROOF_API_HTTP_502', http_status=502,
                    attempt=attempt + 1, maximum_attempts=4, retry_start_window_seconds=600)
                error.close()
                if not _exact_github_api_get(request, error):
                    print(json.dumps(dict(event, decision='STOP_OUTSIDE_EXACT_GET_SCOPE')), flush=True)
                    raise
                if attempt == 3:
                    print(json.dumps(dict(event, decision='STOP_ATTEMPTS_EXHAUSTED')), flush=True)
                    raise
                try:
                    service_delay = _api_502_retry_after(error.headers)
                except (ValueError, TypeError, OverflowError, OSError):
                    print(json.dumps(dict(event, decision='STOP_INVALID_RETRY_AFTER')), flush=True)
                    raise error
                delay = max(float((30, 60, 120)[attempt]), service_delay)
                if time.monotonic() - started + delay >= 600:
                    print(json.dumps(dict(event, decision='STOP_WAIT_EXCEEDS_RETRY_START_WINDOW',
                        requested_wait_seconds=delay)), flush=True)
                    raise
                print(json.dumps(dict(event, decision='RETRY_IDENTICAL_GET_AFTER_WAIT',
                    wait_seconds=delay, service_wait_seconds=service_delay)), flush=True)
                deadline = time.monotonic() + delay
                while time.monotonic() < deadline:
                    remaining = deadline - time.monotonic()
                    if remaining > 0:
                        print(json.dumps(dict(status='WAITING_FOR_EXACT_GITHUB_API_HTTP_502_RETRY',
                            remaining_seconds=round(remaining, 3), no_request_during_wait=True)), flush=True)
                        time.sleep(min(30.0, remaining))
                if time.monotonic() - started >= 600:
                    print(json.dumps(dict(event, decision='STOP_RETRY_WINDOW_AFTER_WAIT')), flush=True)
                    raise
                retry_502_error = error
                continue
            body = error.read(4096).decode('utf-8', errors='replace')
            try: message = json.loads(body).get('message', body)
            except json.JSONDecodeError: message = body
            remaining = error.headers.get('x-ratelimit-remaining')
            reset = error.headers.get('x-ratelimit-reset')
            retry_after = error.headers.get('retry-after')
            delay = None
            if error.code in (403, 429):
                if retry_after and retry_after.isdigit(): delay = int(retry_after) + 1
                elif remaining == '0' and reset and reset.isdigit(): delay = max(1, int(reset) - int(time.time()) + 2)
                elif 'secondary rate limit' in str(message).lower(): delay = 60 * (2 ** attempt)
            print(json.dumps(dict(status='GITHUB_EXACT_PROOF_API_ERROR', http_status=error.code,
                rate_remaining=remaining, rate_reset=reset, retry_after=retry_after,
                message=str(message)[:512], attempt=attempt + 1)), flush=True)
            if delay is None or attempt == 3 or time.monotonic() - started + delay > 3700: raise
            deadline = time.monotonic() + delay
            while time.monotonic() < deadline:
                print(json.dumps(dict(status='WAITING_FOR_DOCUMENTED_GITHUB_RATE_RESET',
                    remaining_seconds=round(deadline - time.monotonic()), no_request_during_wait=True)), flush=True)
                time.sleep(min(30, deadline - time.monotonic()))
    raise AssertionError('Unreachable API retry state')
