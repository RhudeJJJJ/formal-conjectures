#!/usr/bin/env bash
set -euo pipefail
sha256sum -c Proofs/WOWII412FamilyValidation/SHA256SUMS
lake --wfail build FormalConjectures.WrittenOnTheWallII.GraphConjecture412e FormalConjectures.WrittenOnTheWallII.GraphConjecture412ab
mkdir -p .lake/build/lib/lean/Proofs
for mod in WOWII412dCore WOWII412dAssembly CoronaExchange PendantSupport SupportComponentBounds WOWII412eBounds WOWII412abBounds WOWII412FamilyProof WOWII412FamilyAudit; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/${mod}.olean" "Proofs/${mod}.lean"
done
