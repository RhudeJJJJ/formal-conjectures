"""Keep all diagnostics while omitting duplicate prior-module records from stdout.

The verifier still checks every record. Its complete receipt is retained in
the workflow artifact; fresh module records and all errors remain visible.
"""
import json,sys
for line in sys.stdin:
    if line.startswith('COMPLETED_MODULE_JSON '):
        row=json.loads(line.removeprefix('COMPLETED_MODULE_JSON '))
        if row['mode']=='PRIOR_VERIFIED_JOB_EXPORT':continue
    if line.startswith('PASS ') and ' PRIOR_VERIFIED_JOB_EXPORT ' in line:continue
    sys.stdout.write(line);sys.stdout.flush()
