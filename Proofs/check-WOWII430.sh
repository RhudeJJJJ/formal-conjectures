#!/bin/sh
set -eu
export LEAN_NUM_THREADS=1
lake --wfail build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue Mathlib.Combinatorics.SimpleGraph.Diam
mkdir -p .lake/build/lib/lean/Proofs
for module in WOWII430Data WOWII430Proof WOWII430Audit; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/$module.olean" "Proofs/$module.lean"
done
