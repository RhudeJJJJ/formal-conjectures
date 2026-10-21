/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymmetricTangentReserve
import Proofs.RadenkovicGutmanLowStripReserveReduction

/-! Original full reserve on the tangent curve; the exact identity and
the complete mixed-domain polynomial check are both required. -/
namespace Gebendorfer.RadenkovicGutman.SymmetricTangentReserveIdentity
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem data_identity (h c s t : ℝ) (hh : h ≠ 0) (hc : c ≠ 0) (hd : 1-c^2 ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 5 SymmetricTangentReserve.data)
      ![s*t,(s-t)^2,s+t,46*h,2*c] =
    (1685719115165366705018091480285184 : ℝ)*h^4*c^2*(1-c^2)^12*
      LowStripReserveReduction.inner (1/h) (4*c*h/(1-c^2))
        (4*c*h/(1-c^2)+s) (4*c*h/(1-c^2)+t) c := by
  rw [SymmetricTangentReserve.data_eval]
  simp (maxSteps := 10000000) only [LowStripReserveReduction.inner,
    LowStripReserveReduction.core,LowStripReserveReduction.horizontal,
    LowStripReserveReduction.anchor,LowStripReserveReduction.a,LowStripReserveReduction.b,
    LowStripReserveReduction.delta,LowStripDirected.anNegative,LowStripDirected.bdNegative]
  field_simp [hh,hc,hd]
  ring

theorem original_inner_nonneg (h c P Q : ℝ) (hh : h ∈ Ioc (0 : ℝ) (1/46))
    (hc : c ∈ Ioc (0 : ℝ) (1/2))
    (hP : 4*c*h/(1-c^2) ≤ P) (hQ : 4*c*h/(1-c^2) ≤ Q) :
    0 ≤ LowStripReserveReduction.inner (1/h) (4*c*h/(1-c^2)) P Q c := by
  let y := 4*c*h/(1-c^2)
  have hd : 0 < 1-c^2 := by
    have h := pow_le_pow_left₀ hc.1.le hc.2 2
    nlinarith only [h]
  have hs : 0 ≤ P-y := sub_nonneg.mpr hP
  have ht : 0 ≤ Q-y := sub_nonneg.mpr hQ
  have hv : NestedIntegerMixed.Domain 2 3
      ![(P-y)*(Q-y),((P-y)-(Q-y))^2,(P-y)+(Q-y),46*h,2*c] := by
    refine ⟨mul_nonneg hs ht,?_,?_,?_⟩
    · exact sq_nonneg _
    · exact add_nonneg hs ht
    · intro i
      fin_cases i
      · change 46*h ∈ Icc (0 : ℝ) 1
        constructor <;> nlinarith only [hh.1,hh.2]
      · change 2*c ∈ Icc (0 : ℝ) 1
        constructor <;> linarith only [hc.1,hc.2]
  have hp := SymmetricTangentReserve.domain_nonneg _ hv
  rw [data_identity h c (P-y) (Q-y) hh.1.ne' hc.1.ne' hd.ne'] at hp
  have heP : y+(P-y)=P := by ring
  have heQ : y+(Q-y)=Q := by ring
  change 0 ≤ (1685719115165366705018091480285184 : ℝ)*h^4*c^2*(1-c^2)^12*
    LowStripReserveReduction.inner (1/h) y (y+(P-y)) (y+(Q-y)) c at hp
  rw [heP,heQ] at hp
  exact nonneg_of_mul_nonneg_right hp (by positivity)

#print axioms data_identity
#print axioms original_inner_nonneg
end
end Gebendorfer.RadenkovicGutman.SymmetricTangentReserveIdentity
