module
/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
public import Proofs.RGModernRadenkovicGutmanFactoredRoots
public import Proofs.RGModernRadenkovicGutmanCheckedCharpoly

@[expose] public section

/-! Exact finite spectral certificate interfaces. The characteristic polynomial
is bound by complete matrix evaluation certificates, and all root multiplicities
are retained. Exhaustive graph coverage remains an independent obligation. -/
namespace Gebendorfer.RadenkovicGutman.FiniteSpectralCertificates
open scoped Classical
noncomputable section
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem graph_polynomial {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (cs : List ℚ) (hlen : cs.length≤n+1)
    (L U : Fin (n+1) → Matrix (Fin n) (Fin n) ℚ)
    (hc : ∀ k, CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (G.Adj i j)))
        (CheckedCharpoly.sample k))
      (L k) (U k) (CheckedRoots.eval cs (CheckedCharpoly.sample k))=true) :
    (G.lapMatrix ℝ).charpoly=CheckedRoots.polynomial cs :=
  CheckedCharpoly.graph_characteristic_polynomial G cs hlen L U hc

#print axioms graph_polynomial
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.FiniteSpectralCertificates
