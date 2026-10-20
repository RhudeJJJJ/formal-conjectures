/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMinimalFusion
import Proofs.RadenkovicGutmanMixedStopLoss

/-!
# Actual fusion: exact moving-mean integral and threshold transport

Treehood, order, edge counts, integrability and the one-unit count gap are
discharged for the same actual source/fused pair. Positivity of the integral
at the actual mean is necessary and sufficient for strict energy decrease.
A reserve above 2/n at threshold two is a sufficient alternative.
Source: unified manuscript, revised 22 September 2026, Sections 2 and 9.
-/
namespace Gebendorfer.RadenkovicGutman.ActualFusionIntegral
open SimpleGraph CoreQuotient Set MeasureTheory
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]

def delta (C : SimpleGraph V) (u : V) (p q : ℕ) (t : ℝ) : ℝ :=
  stopLoss (laplacianSpectrum (source C u p q)) t -
    stopLoss (laplacianSpectrum (fused C u p q)) t

def normalizedIntegral (C : SimpleGraph V) (u : V) (p q : ℕ) (t : ℝ) : ℝ :=
  (1 / Real.pi) * (∫ y : ℝ in Ioi 0,
    MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) t y)

omit [DecidableEq V] in
theorem source_fused_card (p q : ℕ) :
    Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) =
      Fintype.card (V ⊕ Fin (p + q + 2)) := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem logarithm_integrable (C : SimpleGraph V) (u : V) (p q : ℕ) (t : ℝ) :
    IntegrableOn (MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) t)
      (Ioi 0) :=
  MixedGraphIntegral.integrable _ _ (source_fused_card (V := V) p q) t

theorem source_fused_edges (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    (source C u p q).edgeFinset.card = (fused C u p q).edgeFinset.card := by
  have hs := hT.card_edgeFinset
  have hf := (FusionDescent.fusion_tree_and_leaf_count C u p q hT hd).1.card_edgeFinset
  have hc := source_fused_card (V := V) p q
  omega

theorem integral_eq_delta (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) (t : ℝ) :
    normalizedIntegral C u p q t = delta C u p q t :=
  MixedStopLoss.integral_eq _ _ (source_fused_card (V := V) p q)
    (source_fused_edges C u p q hT hd) t

theorem count_gap (C : SimpleGraph V) (u : V) (p q : ℕ) (t : ℝ) :
    |aboveCount (laplacianSpectrum (source C u p q)) t -
      aboveCount (laplacianSpectrum (fused C u p q)) t| ≤ 1 := by
  have hm := RewireIso.base_missing_edges C u p q
  have h := CountGap.rewire_count_gap (RewireIso.base C u p q)
    (.inl u) (.inr (.inl (Fin.last p))) (.inr (.inr 0))
    (by simp) (by simp) hm.1 hm.2 t
  change |aboveCount (laplacianSpectrum (source C u p q)) t -
    aboveCount (laplacianSpectrum (RewireIso.rewired C u p q)) t| ≤ 1 at h
  rw [MixedStopLoss.aboveCount_iso (RewireIso.fusedIso C u p q) t] at h
  exact h

theorem delta_lipschitz (C : SimpleGraph V) (u : V) (p q : ℕ) (s t : ℝ) :
    |delta C u p q s - delta C u p q t| ≤ |s - t| := by
  have hm := RewireIso.base_missing_edges C u p q
  have h := CountGap.rewire_stopLoss_transport (RewireIso.base C u p q)
    (.inl u) (.inr (.inl (Fin.last p))) (.inr (.inr 0))
    (by simp) (by simp) hm.1 hm.2 s t
  change |(stopLoss (laplacianSpectrum (source C u p q)) s -
      stopLoss (laplacianSpectrum (RewireIso.rewired C u p q)) s) -
    (stopLoss (laplacianSpectrum (source C u p q)) t -
      stopLoss (laplacianSpectrum (RewireIso.rewired C u p q)) t)| ≤ |s - t| at h
  rw [MixedStopLoss.stopLoss_iso (RewireIso.fusedIso C u p q) s,
    MixedStopLoss.stopLoss_iso (RewireIso.fusedIso C u p q) t] at h
  exact h

theorem mean_transport (C : SimpleGraph V) (u : V) (p q : ℕ) :
    delta C u p q 2 - 2 / (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ) ≤
      delta C u p q (2 - 2 /
        (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ)) := by
  have h := delta_lipschitz C u p q (2 - 2 /
    (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ)) 2
  have he : |(2 - 2 / (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ)) - 2| =
      2 / (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ) := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  rw [he, abs_le] at h
  linarith [h.1]

theorem energy_difference (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    laplacianEnergy (source C u p q) - laplacianEnergy (fused C u p q) =
      2 * normalizedIntegral C u p q (2 - 2 /
        (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ)) := by
  have hf := (FusionDescent.fusion_tree_and_leaf_count C u p q hT hd).1
  rw [integral_eq_delta C u p q hT hd]
  unfold delta
  rw [tree_energy_identity _ hT, tree_energy_identity _ hf,
    ← source_fused_card (V := V) p q]
  ring

theorem strict_iff_mean_integral_pos (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) ↔
      0 < normalizedIntegral C u p q (2 - 2 /
        (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ)) := by
  have h := energy_difference C u p q hT hd
  constructor <;> intro hp <;> linarith

theorem strict_of_reserve (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hr : 2 / (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) : ℝ) <
      normalizedIntegral C u p q 2) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  apply (strict_iff_mean_integral_pos C u p q hT hd).mpr
  rw [integral_eq_delta C u p q hT hd]
  rw [integral_eq_delta C u p q hT hd] at hr
  have h := mean_transport C u p q
  linarith

#check @strict_iff_mean_integral_pos
#check @strict_of_reserve
#print axioms source_fused_card
#print axioms logarithm_integrable
#print axioms source_fused_edges
#print axioms integral_eq_delta
#print axioms count_gap
#print axioms delta_lipschitz
#print axioms mean_transport
#print axioms energy_difference
#print axioms strict_iff_mean_integral_pos
#print axioms strict_of_reserve
end
end Gebendorfer.RadenkovicGutman.ActualFusionIntegral
