"""Reject an absent endpoint audit or any non-standard proof axiom."""
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
rows = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
name = "WrittenOnTheWallII.GraphConjecture161.conjecture161"
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert name in rows, "Missing endpoint axiom audit"
for theorem, axioms in rows.items():
    actual = {a.strip() for a in axioms.split(",") if a.strip()}
    assert actual <= allowed, (theorem, actual - allowed)
print("PASS: all audited proof declarations use only the three standard axioms")

