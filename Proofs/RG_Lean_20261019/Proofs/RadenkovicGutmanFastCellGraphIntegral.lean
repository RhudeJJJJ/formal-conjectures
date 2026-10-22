/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastPhysicalCell
import Proofs.RadenkovicGutmanClassGraphRemainders

namespace Gebendorfer.RadenkovicGutman.FastCellGraphIntegral
open CoreQuotient Set MeasureTheory ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_lower (C : SimpleGraph V) (u : V) (p q d : ℕ) (hd : 1 ≤ d)
    (hdegree : C.degree u=d) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (c : FastNestedCellData.Cell) (a b : ℚ)
    (hc : FastNestedCellData.accepts (d : ℚ) c₁ c₂ c=true) (hshape : FastPhysicalCell.shape c a b=true)
    (y : ℝ) (hy : y ∈ Icc (a : ℝ) (b : ℝ)) :
    (c.payment : ℝ) ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (of_decide_eq_true hshape).1
  have hy0 := ha.trans_le hy.1
  obtain ⟨s,hs,hps⟩ := ArmClasses.actual_parameter y hy0 p
  obtain ⟨t,ht,hqt⟩ := ArmClasses.actual_parameter y hy0 q
  rw [hp] at hps
  rw [hq] at hqt
  have hζ := (Focus.schur_in_disk C u y hy0).1
  rw [hdegree] at hζ
  have hdr : (0 : ℝ) < (d : ℚ) := by exact_mod_cast (by omega : 0 < d)
  have hh := FastPhysicalCell.logarithm_lower (d : ℚ) c₁ c₂ c a b hc hshape hdr y hy
    s t hs ht (RootSchur.schurScalar C u (Focus.z y))
    (by simpa only [Rat.cast_natCast] using hζ)
  rw [ClassGraphRemainders.actual_logarithm C u p q y hy0,hps,hqt]
  exact hh

/-- Integrates this exact cell bound on the same actual graph pair. -/
theorem integral_lower (C : SimpleGraph V) (u : V) (p q d : ℕ) (hd : 1 ≤ d)
    (hdegree : C.degree u=d) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (c : FastNestedCellData.Cell) (a b : ℚ)
    (hc : FastNestedCellData.accepts (d : ℚ) c₁ c₂ c=true) (hshape : FastPhysicalCell.shape c a b=true) :
    ((b : ℝ)-(a : ℝ))*(c.payment : ℝ) ≤ ∫ y : ℝ in (a : ℝ)..(b : ℝ),
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (of_decide_eq_true hshape).1
  have hab : (a : ℝ) ≤ b := by exact_mod_cast (of_decide_eq_true hshape).2.1.le
  have hfi := TailIntegral.interval_integrable_of_Ioi (logarithm_integrable C u p q 2) ha.le hab
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hfi
    (fun y hy => graph_lower C u p q d hd hdegree c₁ c₂ hp hq c a b hc hshape y hy)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using h

#print axioms graph_lower
#print axioms integral_lower
end
end Gebendorfer.RadenkovicGutman.FastCellGraphIntegral
