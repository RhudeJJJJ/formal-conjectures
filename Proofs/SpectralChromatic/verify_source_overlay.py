"""Verify the exact declared differences of the standalone import overlay.

This compares source bytes after two explicit transformations. It does not
claim the queued canonical-original-import CI has run.
"""
from pathlib import Path
import hashlib,json
b=Path(__file__).resolve().parents[2]
original=(b/'Proofs/SpectralChromatic/OriginalSource.txt').read_text(encoding='utf8')
overlay=(b/'FormalConjectures/Paper/AouchicheHansenStevanovicSpectralChromatic.lean').read_text(encoding='utf8')
imports=(b/'Proofs/SpectralChromatic/reduced-imports.txt').read_text(encoding='utf8').strip()
assert original.count('public import FormalConjecturesUtil')==1
assert original.count('@[category research solved, AMS 5]\n')==3
expected=original.replace('public import FormalConjecturesUtil',imports).replace('@[category research solved, AMS 5]\n','')
assert overlay==expected,'Unexpected change in a mathematical definition or target declaration'
report={'status':'exact_source_overlay_verified','original_sha256':hashlib.sha256(original.encode()).hexdigest(),'overlay_sha256':hashlib.sha256(overlay.encode()).hexdigest(),'transformations':['Replace only the single umbrella import with the listed pinned Mathlib imports','Remove exactly the three category/AMS attributes'],'all_other_source_characters_identical':True,'scope':'All mathematical definitions, hypotheses, target types, namespaces and admitted negative-control statements retained verbatim. Does not assert canonical original-import CI completion.'}
(b/'Proofs/SpectralChromatic/source-overlay-receipt.json').write_text(json.dumps(report,indent=2),encoding='utf8')
print(json.dumps(report))
