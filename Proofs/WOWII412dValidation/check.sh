#!/usr/bin/env bash
set -euo pipefail
sha256sum -c Proofs/WOWII412dValidation/SHA256SUMS
lake --wfail build FormalConjectures.WrittenOnTheWallII.GraphConjecture412d
mkdir -p .lake/build/lib/lean/Proofs
for mod in WOWII412dCore WOWII412dAssembly StrictHallForest RankedForestCover WOWII412dForest WOWII412dCover WOWII412dProof WOWII412dAudit; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/${mod}.olean" "Proofs/${mod}.lean"
done
