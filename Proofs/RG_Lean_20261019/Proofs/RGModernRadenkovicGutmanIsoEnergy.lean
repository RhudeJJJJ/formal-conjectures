module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Laplacian characteristic polynomials, spectral sums and energy are invariant
under graph isomorphisms, including isomorphisms between different vertex types.
-/
public import Proofs.RGModernRadenkovicGutmanSpectral
public import Proofs.RGModernRadenkovicGutmanRewireIso

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Gebendorfer.RadenkovicGutman.IsoEnergy
open Matrix
open scoped Classical
noncomputable section

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem laplacian_reindex {𝕜 : Type*} [CommRing 𝕜]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    Matrix.reindex f.toEquiv f.toEquiv (G.lapMatrix 𝕜) = H.lapMatrix 𝕜 := by
  ext i j
  change (G.lapMatrix 𝕜) (f.symm i) (f.symm j) = (H.lapMatrix 𝕜) i j
  have hd := f.degree_eq (f.symm i)
  rw [RelIso.apply_symm_apply] at hd
  have he : (f.symm i = f.symm j) ↔ i = j := f.symm.injective.eq_iff
  have ha : G.Adj (f.symm i) (f.symm j) ↔ H.Adj i j := f.symm.map_adj_iff
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply,
    he, ha, hd]

theorem charpoly_eq {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    (G.lapMatrix ℝ).charpoly = (H.lapMatrix ℝ).charpoly := by
  rw [← laplacian_reindex f, Matrix.charpoly_reindex]

theorem spectral_sum_roots (G : SimpleGraph V) (φ : ℝ → ℝ) :
    (∑ i, φ (laplacianSpectrum G i)) =
      ((G.lapMatrix ℝ).charpoly.roots.map φ).sum := by
  rw [(G.isHermitian_lapMatrix ℝ).roots_charpoly_eq_eigenvalues]
  rw [Multiset.map_map]
  rfl

theorem spectral_sum_eq {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (φ : ℝ → ℝ) :
    (∑ i, φ (laplacianSpectrum G i)) = (∑ j, φ (laplacianSpectrum H j)) := by
  rw [spectral_sum_roots, spectral_sum_roots, charpoly_eq f]

omit [DecidableEq V] [DecidableEq W] in
theorem meanDegree_eq {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    meanDegree G = meanDegree H := by
  simp only [meanDegree, f.card_edgeFinset_eq, Fintype.card_congr f.toEquiv]

theorem energy_eq {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    laplacianEnergy G = laplacianEnergy H := by
  unfold laplacianEnergy centredEnergy
  rw [meanDegree_eq f]
  exact spectral_sum_eq f (fun x => |x - meanDegree H|)

theorem fused_energy (C : SimpleGraph V) (u : V) (p q : ℕ) :
    laplacianEnergy (RewireIso.rewired C u p q) =
      laplacianEnergy (CoreQuotient.fused C u p q) :=
  energy_eq (RewireIso.fusedIso C u p q)

#print axioms laplacian_reindex
#print axioms charpoly_eq
#print axioms spectral_sum_eq
#print axioms energy_eq
#print axioms fused_energy

attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.IsoEnergy
