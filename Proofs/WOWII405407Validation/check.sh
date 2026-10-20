#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
sha256sum --check Proofs/WOWII405407Validation/SHA256SUMS
lake --wfail build FormalConjectures.WrittenOnTheWallII.GraphConjecture404To407
mkdir -p .lake/build/lib/lean/Proofs
for module in WOWII412dCore CoronaTwoDominatingProof WOWII405407Proof WOWII405407Audit; do
  lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o ".lake/build/lib/lean/Proofs/${module}.olean" "Proofs/${module}.lean"
done
