"""Respect explicit GitHub API rate limits without retrying permission failures."""
import json, time, urllib.error, urllib.request


def api_open(request, opener=None):
    if opener is None: opener = urllib.request.urlopen
    started = time.monotonic()
    for attempt in range(4):
        try:
            return opener(request, timeout=120)
        except urllib.error.HTTPError as error:
            if error.code in (301, 302, 303, 307, 308): raise
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
