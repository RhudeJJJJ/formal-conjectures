/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymmetricConstantReserve
import Proofs.RadenkovicGutmanLowStripReserveReduction
namespace Gebendorfer.RadenkovicGutman.SymmetricConstantReserveIdentity
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem data_identity (v y s t : ℝ) (hy : y ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 5 SymmetricConstantReserve.data)
      ![v,s*t,(s-t)^2,s+t,2*y] =
    (84934656 : ℝ)*y^4*LowStripReserveReduction.inner (8/(3*y)+v) y (y+s) (y+t) 1 := by
  rw [SymmetricConstantReserve.data_eval]
  simp (maxSteps := 10000000) only [LowStripReserveReduction.inner,
    LowStripReserveReduction.core,LowStripReserveReduction.horizontal,
    LowStripReserveReduction.anchor,LowStripReserveReduction.a,LowStripReserveReduction.b,
    LowStripReserveReduction.delta,LowStripDirected.anNegative,LowStripDirected.bdNegative]
  field_simp [hy]
  ring

theorem original_inner_nonneg (v y P Q : ℝ) (hv : 0 ≤ v)
    (hy : y ∈ Ioc (0 : ℝ) (1/2)) (hP : y ≤ P) (hQ : y ≤ Q) :
    0 ≤ LowStripReserveReduction.inner (8/(3*y)+v) y P Q 1 := by
  have hs : 0 ≤ P-y := sub_nonneg.mpr hP
  have ht : 0 ≤ Q-y := sub_nonneg.mpr hQ
  have hx : NestedIntegerMixed.Domain 1 4
      ![v,(P-y)*(Q-y),((P-y)-(Q-y))^2,(P-y)+(Q-y),2*y] := by
    refine ⟨hv,mul_nonneg hs ht,sq_nonneg _,add_nonneg hs ht,?_⟩
    intro i
    fin_cases i
    change 2*y ∈ Icc (0 : ℝ) 1
    constructor <;> linarith only [hy.1,hy.2]
  have hp := SymmetricConstantReserve.domain_nonneg _ hx
  rw [data_identity v y (P-y) (Q-y) hy.1.ne'] at hp
  have heP : y+(P-y)=P := by ring
  have heQ : y+(Q-y)=Q := by ring
  rw [heP,heQ] at hp
  have hy0 : 0 < y := hy.1
  exact nonneg_of_mul_nonneg_right hp (by positivity)

#print axioms data_identity
#print axioms original_inner_nonneg
end
end Gebendorfer.RadenkovicGutman.SymmetricConstantReserveIdentity
