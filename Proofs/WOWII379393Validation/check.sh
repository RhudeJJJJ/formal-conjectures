#!/usr/bin/env bash
set -euo pipefail
sha256sum -c Proofs/WOWII379393Validation/SHA256SUMS
lake --wfail build FormalConjectures.WrittenOnTheWallII.GraphConjecture379 FormalConjectures.WrittenOnTheWallII.GraphConjecture393 > Proofs/WOWII379393Validation/statement-build.log 2>&1
mkdir -p .lake/build/lib/lean/Proofs
for mod in WOWII412dCore WOWII412dAssembly CoronaExchange PendantSupport FiniteMatchingCover ForestCounting EdgePartitionCounts TotalDominationForestBudget WOWII393aProof WOWII379Proof WOWII379393Audit; do
  if ! lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/${mod}.olean" "Proofs/${mod}.lean" \
    > "Proofs/WOWII379393Validation/${mod}.log" 2>&1; then
    cat "Proofs/WOWII379393Validation/${mod}.log"
    exit 1
  fi
  printf 'PASS %s\n' "$mod"
done
