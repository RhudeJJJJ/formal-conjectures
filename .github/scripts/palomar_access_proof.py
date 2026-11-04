"""Create/read/delete only this task's temporary exact-commit Git tags.

Runs in a separate trusted GitHub Actions job. Never accepts a Palomar pending
secret or access token. The actual source snapshot is frozen and not updated.
"""
import json
import os
from pathlib import Path
import re
import subprocess

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
SOURCE = '981e9d7f797cbf512d2f467661f71e2d5871f5d5'

def api(method, endpoint, body=None, absent_ok=False):
    command = ['gh', 'api', '--method', method, endpoint]
    if body is not None:
        command += ['--input', '-']
    result = subprocess.run(command, input=json.dumps(body) if body is not None else None,
                            text=True, capture_output=True, check=False)
    if result.returncode:
        if absent_ok and 'HTTP 404' in result.stderr:
            return None
        # gh errors identify endpoints/status; no authorization header is logged.
        raise RuntimeError(result.stderr.strip())
    return json.loads(result.stdout) if result.stdout.strip() else {}

def create(tag):
    endpoint = f'repos/{REPOSITORY}/git/ref/tags/{tag}'
    if api('GET', endpoint, absent_ok=True) is not None:
        raise RuntimeError('Ref already exists; refusing to overwrite it')
    data = api('POST', f'repos/{REPOSITORY}/git/refs',
               {'ref': 'refs/tags/' + tag, 'sha': SOURCE})
    actual = api('GET', endpoint)
    if actual.get('object', {}).get('type') != 'commit' or actual['object']['sha'] != SOURCE:
        raise RuntimeError('Tag readback does not match the frozen source commit')
    print(json.dumps({'operation': 'create', 'ref': data['ref'],
                      'source': SOURCE, 'readback': 'exact'}))

def remove(tag):
    endpoint = f'repos/{REPOSITORY}/git/ref/tags/{tag}'
    actual = api('GET', endpoint, absent_ok=True)
    if actual is None:
        print(json.dumps({'operation': 'delete', 'tag': tag, 'already_absent': True}))
        return
    if actual.get('object', {}).get('type') != 'commit' or actual['object']['sha'] != SOURCE:
        raise RuntimeError('Ref identity changed; refusing to remove it')
    api('DELETE', f'repos/{REPOSITORY}/git/refs/tags/{tag}')
    if api('GET', endpoint, absent_ok=True) is not None:
        raise RuntimeError('Tag remains after cleanup')
    print(json.dumps({'operation': 'delete', 'tag': tag, 'readback': 'absent'}))

def main():
    if os.environ.get('GITHUB_REPOSITORY') != REPOSITORY:
        raise RuntimeError('Wrong repository for this scoped helper')
    payload = json.loads(Path('palomar-access.json').read_text(encoding='utf-8'))
    if set(payload) - {'operation', 'challenge', 'commit'} or payload.get('commit') != SOURCE:
        raise RuntimeError('Unexpected payload fields or source commit')
    operation = payload.get('operation')
    if operation == 'probe':
        run_id = os.environ.get('GITHUB_RUN_ID', '')
        if not re.fullmatch(r'[0-9]{1,24}', run_id):
            raise RuntimeError('Invalid workflow run identifier')
        tag = 'palomar-agent-readiness-7385-' + run_id
        create(tag)
        remove(tag)
        return
    challenge = payload.get('challenge', '')
    if not re.fullmatch(r'[A-Za-z0-9_-]{8,128}', challenge):
        raise RuntimeError('Invalid challenge; no ref changes made')
    tag = 'palomar-verify-' + challenge
    if operation == 'create':
        create(tag)
    elif operation == 'delete':
        remove(tag)
    else:
        raise RuntimeError('Unsupported operation; no ref changes made')

if __name__ == '__main__':
    main()
