#!/usr/bin/env bash
set -euo pipefail
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Tactic
lake --wfail build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
mkdir -p .lake/build/lib/lean/Proofs
for module in WOWII381Proof WOWII381Audit; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/$module.olean" "Proofs/$module.lean" \
    | tee "/tmp/$module-axioms.log"
  if rg 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' "/tmp/$module-axioms.log"; then
    exit 1
  fi
done
