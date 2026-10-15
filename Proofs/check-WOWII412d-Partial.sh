#!/bin/sh
set -eu
export LEAN_NUM_THREADS=1
lake --wfail build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
mkdir -p .lake/build/lib/lean/Proofs
for module in WOWII412dCore WOWII412dAssembly; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/$module.olean" "Proofs/$module.lean"
done
