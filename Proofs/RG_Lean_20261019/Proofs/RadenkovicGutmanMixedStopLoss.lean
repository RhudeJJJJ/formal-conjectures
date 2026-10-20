/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMixedGraphIntegral

/-! Exact Coulson stop-loss identity across the actual distinct vertex types. -/
namespace Gebendorfer.RadenkovicGutman.MixedStopLoss
open SimpleGraph Set MeasureTheory
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem stopLoss_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (t : ℝ) :
    stopLoss (laplacianSpectrum G) t = stopLoss (laplacianSpectrum H) t := by
  unfold stopLoss
  exact IsoEnergy.spectral_sum_eq f (fun x => max (x - t) 0)

theorem aboveCount_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (t : ℝ) :
    aboveCount (laplacianSpectrum G) t = aboveCount (laplacianSpectrum H) t := by
  unfold aboveCount
  exact IsoEnergy.spectral_sum_eq f (fun x => if t < x then 1 else 0)

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

#print axioms stopLoss_iso
#print axioms aboveCount_iso
#print axioms integral_eq
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.MixedStopLoss
