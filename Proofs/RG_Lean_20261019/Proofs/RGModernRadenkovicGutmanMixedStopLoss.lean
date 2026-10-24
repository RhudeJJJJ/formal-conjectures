module
/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
public import Proofs.RGModernRadenkovicGutmanMixedGraphIntegral

@[expose] public section

/-! Exact Coulson stop-loss identity across distinct vertex types and adjacency deciders. -/
namespace Gebendorfer.RadenkovicGutman.MixedStopLoss
open SimpleGraph Set MeasureTheory
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem spectral_sum_iso {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H) (φ : ℝ → ℝ) :
    (∑ i, φ (laplacianSpectrum G i)) = (∑ i, φ (laplacianSpectrum H i)) := by
  calc
    _ = ∑ i, φ (@laplacianSpectrum V _ _ G
        (fun a b => Classical.propDecidable (G.Adj a b)) i) :=
      congrArg (fun d => ∑ i, φ (@laplacianSpectrum V _ _ G d i)) (Subsingleton.elim _ _)
    _ = ∑ i, φ (@laplacianSpectrum W _ _ H
        (fun a b => Classical.propDecidable (H.Adj a b)) i) :=
      IsoEnergy.spectral_sum_eq f φ
    _ = _ := congrArg (fun d => ∑ i, φ (@laplacianSpectrum W _ _ H d i))
      (Subsingleton.elim _ _)

theorem stopLoss_iso {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H) (t : ℝ) :
    stopLoss (laplacianSpectrum G) t = stopLoss (laplacianSpectrum H) t := by
  unfold stopLoss
  exact spectral_sum_iso f (fun x => max (x - t) 0)

theorem aboveCount_iso {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H) (t : ℝ) :
    aboveCount (laplacianSpectrum G) t = aboveCount (laplacianSpectrum H) t := by
  unfold aboveCount
  exact spectral_sum_iso f (fun x => if t < x then 1 else 0)

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem rewire_count_gap_iso (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    {S : SimpleGraph W} {H : SimpleGraph U} [DecidableRel S.Adj] [DecidableRel H.Adj]
    (f : (G ⊔ edge u w) ≃g S) (g : (G ⊔ edge v w) ≃g H) (t : ℝ) :
    |aboveCount (laplacianSpectrum S) t - aboveCount (laplacianSpectrum H) t| ≤ 1 := by
  have h := CountGap.rewire_count_gap G u v w huw hvw hguw hgvw t
  rw [aboveCount_iso f t, aboveCount_iso g t] at h
  exact h

theorem rewire_stopLoss_transport_iso (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    {S : SimpleGraph W} {H : SimpleGraph U} [DecidableRel S.Adj] [DecidableRel H.Adj]
    (f : (G ⊔ edge u w) ≃g S) (g : (G ⊔ edge v w) ≃g H) (s t : ℝ) :
    |(stopLoss (laplacianSpectrum S) s - stopLoss (laplacianSpectrum H) s) -
      (stopLoss (laplacianSpectrum S) t - stopLoss (laplacianSpectrum H) t)| ≤ |s-t| := by
  have h := CountGap.rewire_stopLoss_transport G u v w huw hvw hguw hgvw s t
  rw [stopLoss_iso f s, stopLoss_iso g s, stopLoss_iso f t, stopLoss_iso g t] at h
  exact h

theorem integral_eq (G : SimpleGraph V) (H : SimpleGraph W)
    (hc : Fintype.card V = Fintype.card W)
    (he : G.edgeFinset.card = H.edgeFinset.card) (t : ℝ) :
    (1 / Real.pi) * (∫ y : ℝ in Ioi 0, MixedGraphIntegral.logarithm G H t y) =
      stopLoss (laplacianSpectrum G) t - stopLoss (laplacianSpectrum H) t := by
  let e : V ≃ W := Fintype.equivOfCardEq hc
  let H' : SimpleGraph V := H.comap e
  let f : H' ≃g H := { toEquiv := e, map_rel_iff' := by intro a b; rfl }
  have hlog : MixedGraphIntegral.logarithm G H t =
      GraphIntegral.graphLogarithm G H' t := by
    funext y
    unfold MixedGraphIntegral.logarithm GraphIntegral.graphLogarithm
    rw [MixedGraphIntegral.shifted_det_eq f]
  have he' : G.edgeFinset.card = H'.edgeFinset.card :=
    he.trans f.card_edgeFinset_eq.symm
  rw [hlog, GraphIntegral.graph_stopLoss_integral G H' he' t, stopLoss_iso f t]

#print axioms spectral_sum_iso
#print axioms stopLoss_iso
#print axioms aboveCount_iso
#print axioms rewire_count_gap_iso
#print axioms rewire_stopLoss_transport_iso
#print axioms integral_eq
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.MixedStopLoss
