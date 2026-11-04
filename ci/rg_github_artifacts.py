"""Fetch a hash-bound original GitHub artifact; respect explicit rate-limit headers."""
import email.utils,hashlib,json,math,os,time,urllib.error,urllib.parse,urllib.request

SIGNED_503_MAX_ATTEMPTS = 4
SIGNED_503_BACKOFF_SECONDS = (30, 60, 120)
SIGNED_503_RETRY_START_WINDOW_SECONDS = 600


def _service_retry_delay(headers):
    """Respect explicit service waits; an invalid supplied wait stops retries."""
    delay = 0.0
    for name in ('Retry-After', 'retry-after-ms', 'x-ms-retry-after-ms'):
        raw = headers.get(name)
        if raw is None:
            continue
        value = raw.strip()
        if not value or len(value) > 128:
            raise ValueError('Invalid service retry header')
        if value.isascii() and value.isdigit():
            seconds = float(int(value)) / (1000 if name.endswith('-ms') else 1)
        elif name == 'Retry-After':
            date = email.utils.parsedate_to_datetime(value)
            if date.tzinfo is None:
                raise ValueError('Retry date has no timezone')
            seconds = max(0.0, date.timestamp() - time.time())
        else:
            raise ValueError('Retry milliseconds must be an integer')
        if not math.isfinite(seconds):
            raise ValueError('Service retry delay is not finite')
        delay = max(delay, seconds)
    return delay


def _download_signed_archive(get_archive_location):
    """Retry only a signed GET's HTTP 503 for the same fixed artifact.

    The 600-second window bounds eligibility to start another retry; the
    existing 120-second socket timeout still applies to each request/read.
    Resolve a fresh GitHub redirect after each wait: signed links expire.
    Existing API rate-limit waits never reset this monotonic window. If they
    exhaust it, no subsequent signed GET starts. This is not a hard deadline
    for the pre-existing API rate-limit handling or an in-flight transfer.
    Hash and original-run checks remain in fetch_archive after this returns.
    """
    started = time.monotonic()
    last_service_error = None
    for attempt in range(1, SIGNED_503_MAX_ATTEMPTS + 1):
        if last_service_error is not None and time.monotonic() - started > SIGNED_503_RETRY_START_WINDOW_SECONDS:
            raise last_service_error
        # This callback always addresses the original, hash-bound artifact ID.
        # Its API errors keep the pre-existing API handling and are not caught
        # by the signed-download HTTP-503 retry handler below.
        destination, inline_data = get_archive_location()
        if last_service_error is not None and time.monotonic() - started > SIGNED_503_RETRY_START_WINDOW_SECONDS:
            print(json.dumps(dict(status='SIGNED_ARCHIVE_HTTP_503', attempt=attempt,
                                  decision='STOP_RETRY_WINDOW_ELAPSED_DURING_REDIRECT')), flush=True)
            raise last_service_error
        if inline_data is not None:
            assert destination is None and isinstance(inline_data, bytes)
            return inline_data
        assert isinstance(destination, str)
        try:
            # The signed external download receives no GitHub authorization.
            with urllib.request.urlopen(destination, timeout=120) as response:
                return response.read()
        except urllib.error.HTTPError as error:
            if error.code != 503:
                raise
            last_service_error = error
            service_code = error.headers.get('x-ms-error-code', '')
            service_code = service_code if service_code.isascii() and service_code.isalnum() and len(service_code) <= 128 else None
            event = dict(status='SIGNED_ARCHIVE_HTTP_503', attempt=attempt,
                maximum_attempts=SIGNED_503_MAX_ATTEMPTS,
                retry_start_window_seconds=SIGNED_503_RETRY_START_WINDOW_SECONDS,
                service_error_code=service_code,
                has_retry_after=error.headers.get('Retry-After') is not None,
                has_retry_after_ms_generic=error.headers.get('retry-after-ms') is not None,
                has_retry_after_ms=error.headers.get('x-ms-retry-after-ms') is not None)
            error.close()
            if attempt == SIGNED_503_MAX_ATTEMPTS:
                print(json.dumps(dict(event, decision='STOP_ATTEMPTS_EXHAUSTED')), flush=True)
                raise
            try:
                service_delay = _service_retry_delay(error.headers)
            except (ValueError, TypeError, OverflowError, OSError):
                print(json.dumps(dict(event, decision='STOP_INVALID_SERVICE_RETRY_HEADER')), flush=True)
                raise error
            delay = max(float(SIGNED_503_BACKOFF_SECONDS[attempt - 1]), service_delay)
            if time.monotonic() - started + delay > SIGNED_503_RETRY_START_WINDOW_SECONDS:
                print(json.dumps(dict(event, decision='STOP_SERVICE_WAIT_EXCEEDS_RETRY_WINDOW',
                                      requested_wait_seconds=delay)), flush=True)
                raise
            print(json.dumps(dict(event, decision='RETRY_SAME_ARTIFACT_WITH_FRESH_REDIRECT_AFTER_WAIT',
                                  wait_seconds=delay, documented_service_wait_seconds=service_delay)), flush=True)
            deadline = time.monotonic() + delay
            while time.monotonic() < deadline:
                remaining = deadline - time.monotonic()
                if remaining > 0:
                    print(json.dumps(dict(status='WAITING_FOR_SIGNED_ARCHIVE_SERVICE',
                                          remaining_seconds=round(remaining, 3),
                                          no_request_during_wait=True)), flush=True)
                    time.sleep(min(30.0, remaining))
            if time.monotonic() - started > SIGNED_503_RETRY_START_WINDOW_SECONDS:
                print(json.dumps(dict(event, decision='STOP_RETRY_START_WINDOW_ELAPSED')), flush=True)
                raise
    raise AssertionError('Unreachable signed download retry state')

def fetch_archive(m):
    token=os.environ['GITHUB_TOKEN']
    api=f"https://api.github.com/repos/{m['repository']}/actions/artifacts/{m['artifact_id']}"
    headers={'Authorization':'Bearer '+token,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'}
    def api_open(url,opener=urllib.request.urlopen):
     started=time.monotonic()
     for attempt in range(4):
      try:return opener(urllib.request.Request(url,headers=headers),timeout=120)
      except urllib.error.HTTPError as error:
       if error.code in (301,302,303,307,308):raise
       body=error.read(4096).decode('utf-8',errors='replace')
       try:message=json.loads(body).get('message',body)
       except json.JSONDecodeError:message=body
       remaining=error.headers.get('x-ratelimit-remaining')
       reset=error.headers.get('x-ratelimit-reset')
       retry_after=error.headers.get('retry-after')
       print(json.dumps({'status':'GITHUB_ARTIFACT_API_ERROR','http_status':error.code,
         'rate_remaining':remaining,'rate_reset':reset,'retry_after':retry_after,
         'message':str(message)[:512],'attempt':attempt+1}),flush=True)
       delay=None
       if error.code in (403,429):
        if retry_after and retry_after.isdigit():delay=int(retry_after)+1
        elif remaining=='0' and reset and reset.isdigit():delay=max(1,int(reset)-int(time.time())+2)
        elif 'secondary rate limit' in str(message).lower():delay=60*(2**attempt)
       if delay is None or attempt==3 or time.monotonic()-started+delay>3700:raise
       deadline=time.monotonic()+delay
       while time.monotonic()<deadline:
        wait=min(30,deadline-time.monotonic())
        print(json.dumps({'status':'WAITING_FOR_DOCUMENTED_GITHUB_RATE_RESET',
          'remaining_seconds':round(deadline-time.monotonic()),'no_request_during_wait':True}),flush=True)
        time.sleep(wait)
     raise AssertionError('Unreachable API retry state')
    def get(url):
     with api_open(url) as r:return r.read()
    meta=json.loads(get(api))
    assert not meta['expired'] and meta['digest']=='sha256:'+m['artifact_sha256']
    assert meta['workflow_run']['id']==m['run'] and meta['workflow_run']['head_sha']==m['source_commit']
    class NoRedirect(urllib.request.HTTPRedirectHandler):
     def redirect_request(self,req,fp,code,msg,hdrs,newurl):return None
    def get_archive_location():
     try:
      with api_open(api+'/zip',urllib.request.build_opener(NoRedirect).open) as r:
       return None,r.read()
     except urllib.error.HTTPError as e:
      assert e.code in (301,302,303,307,308)
      destination=e.headers['Location']
      e.close()
      parsed=urllib.parse.urlparse(destination)
      assert parsed.scheme=='https' and parsed.hostname and not parsed.username and not parsed.password
      return destination,None
    data=_download_signed_archive(get_archive_location)
    assert hashlib.sha256(data).hexdigest()==m['artifact_sha256']
    return data
