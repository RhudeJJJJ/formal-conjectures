/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLongArmGeometry1L
import Proofs.RadenkovicGutmanNestedHornerTransform
import Proofs.RadenkovicGutmanLongArmBothCoefficientUAll
import Proofs.RadenkovicGutmanLongArmBothCoefficientV
import Proofs.RadenkovicGutmanLongArmBothCoefficientJAll
namespace Gebendorfer.RadenkovicGutman.LongArmBothAllDegrees
open Focus CoreQuotient Set MeasureTheory LongArmBothFamily
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem coefficient_U (d y v t : ℝ) (hy : 0 < y) : Complex.normSq (b d y (P y v) (Q y t) * star (e d y (P y v) (Q y t)) - a d (P y v) (Q y t) * star (c d y (P y v) (Q y t))) = scaleFactor y v t * up d y v t := by
  exact LongArmBothFamily.coefficient_U_all d y v t hy
#print axioms coefficient_U
theorem coefficient_J (d y v t : ℝ) (hy : 0 < y) : (Complex.normSq (b d y (P y v) (Q y t)) - Complex.normSq (a d (P y v) (Q y t)))^2 = scaleFactor y v t * jp d y v t := by
  exact LongArmBothFamily.coefficient_J_all d y v t hy
#print axioms coefficient_J
theorem log_lower (d L s y v t : ℝ) (hd : 0 < d) (hL : 0 < L) (hs : 0 < s) (hy : 0 < y)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hm : 0 ≤ jp d y v t-L*((1+s)*up d y v t+(1+1/s)*vp d y v t))
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    Real.log L/2 ≤ Real.log ‖quotient y (P y v) (Q y t) ζ‖ := by
  have hbound : L ≤ ‖quotient y (P y v) (Q y t) ζ‖^2 := by
    apply concrete_certificate d y (P y v) (Q y t) hd hy
      (LongArmFamily1L.Q_ge y v hy hv.1) (LongArmFamily1L.Q_ge y t hy ht.1) ζ hζ s L hs
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, coefficient_U d y v t hy,
      coefficient_V d y v t hy, coefficient_J d y v t hy]
    nlinarith only [mul_nonneg (scaleFactor_nonneg y v t hy) hm]
  have hn : 0 < ‖quotient y (P y v) (Q y t) ζ‖ := by
    have := norm_nonneg (quotient y (P y v) (Q y t) ζ)
    nlinarith
  have hl := Real.log_le_log hL hbound
  rw [Real.log_pow] at hl
  norm_num at hl
  simp only [one_div] at *
  linarith only [hl]
variable {U : Type*} [Fintype U] [DecidableEq U]
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
theorem graph_lower (C : SimpleGraph U) (u : U) (p q D : ℕ) (hd : C.degree u = D)
    (hp : 4 ≤ p) (hq : 4 ≤ q) (B y : ℝ) (hy : 0 < y)
    (hm : ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ : ℂ, ‖ζ-g D y‖ ≤ r D y →
      B ≤ Real.log ‖quotient y (P y v) (Q y t) ζ‖) :
    B ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  obtain ⟨v, hv, heP⟩ := LongArmFamily1L.actual_q y hy p hp
  obtain ⟨t, ht, heQ⟩ := LongArmFamily1L.actual_q y hy q hq
  have hζ := (schur_in_disk C u y hy).1
  rw [hd] at hζ
  have hl := hm v hv t ht _ hζ
  change B ≤ Real.log ‖(shifted (z y) (source C u p q)).det / (shifted (z y) (fused C u p q)).det‖
  rw [concrete_graph_quotient C u y hy p q, heP, heQ]
  exact hl
#print axioms log_lower
#print axioms graph_lower
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LongArmBothAllDegrees
