#!/usr/bin/env bash
set -euo pipefail
python3 Proofs/SpectralChromatic/verify_source_overlay.py
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Extremal.Turan Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex Mathlib.Combinatorics.SimpleGraph.AdjMatrix Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs Mathlib.Analysis.Real.Sqrt Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Linarith Mathlib.Tactic.FinCases
mkdir -p .lake/build/lib/lean/FormalConjectures/Paper .lake/build/lib/lean/Proofs/SpectralChromatic
lake env lean -DwarningAsError=false -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/FormalConjectures/Paper/AouchicheHansenStevanovicSpectralChromatic.olean FormalConjectures/Paper/AouchicheHansenStevanovicSpectralChromatic.lean
for name in Full ExactAudit; do
 lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false -o ".lake/build/lib/lean/Proofs/SpectralChromatic/$name.olean" "Proofs/SpectralChromatic/$name.lean"
done
