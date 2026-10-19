#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname -- "$0")/.."
lake exe cache get
lake --wfail build FormalConjectures.Paper.TotalDominationAnnihilation
mkdir -p .lake/build/lib/lean/Proofs
modules=(
  TDABudget TDAHypergraphBase ZajacBrooks TDAUniform TDAMixedBase TDAMixed
  TDAOptimal TDADegreeBudget TDANeighborhood TDAGraphBasics TDACoreCover
  TDALeafCounts TDAGeneralBound TDAGraphBudget TDATreeColor TDATreeBound
  TDATransfer TDAGraphEdge TDAMaxTwo TDACycleEdge TDAFull TDACertificate
)
for module in "${modules[@]}"; do
  lake env lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/Proofs/$module.olean" "Proofs/$module.lean"
done
if [[ "${1:-}" == "--full" ]]; then
  lake --wfail build
fi
