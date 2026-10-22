/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastArmCoverIntegral

namespace Gebendorfer.RadenkovicGutman.PaidFixedClassIntegral
set_option maxHeartbeats 0

def accepts (T P : ℚ) : Bool :=
  decide (0 ≤ T ∧ T*(22/7) < -9/1000+P-1/2048)

noncomputable section
open CoreQuotient Set MeasureTheory ActualFusionIntegral
open scoped Classical

/-- A checked class partition pays any nonnegative rational reserve at any
positive root degree, on the original source and fused Laplace matrices. -/
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q d : ℕ) (hd : 1 ≤ d)
    (hdegree : C.degree u=d) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (T : ℚ) (cs : List FastArmCoverIntegral.Slice)
    (hcheck : FastArmCoverIntegral.checkAt (d : ℚ) c₁ c₂ (1/1000) 1024 cs=true)
    (hbudget : accepts T (FastArmCoverIntegral.payment cs)=true) :
    (T : ℝ) < normalizedIntegral C u p q 2 := by
  let a : ℝ := ((1/1000 : ℚ) : ℝ)
  let Y : ℝ := ((1024 : ℚ) : ℝ)
  let B : ℝ := (FastArmCoverIntegral.payment cs : ℝ)
  have hB := FastArmCoverIntegral.integral_lower C u p q d hd hdegree c₁ c₂ hp hq
    (1/1000) 1024 (by norm_num) cs hcheck
  have hroot : 1 ≤ C.degree u := by omega
  have hnorm := ClassGraphRemainders.normalized_lower_of_finite_payment C u p q
    hroot a Y B (by norm_num [a]) (by norm_num [a]) (by norm_num [Y]) hB
  have hl := RationalLog.sound (1/6250000) (-8) 23 32 FastPaidDegreeOneClass.origin_log_checked
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_neg] at hl
  rw [show (1/6250000 : ℝ)=(2*(1/1000 : ℝ)/5)^2 by norm_num,Real.log_pow] at hl
  have hlog : (-8 : ℝ) ≤ Real.log (2*a/5) := by
    dsimp [a]
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    linarith only [hl]
  have ho : (-9/1000 : ℝ) ≤ a*(Real.log (2*a/5)-1) := by
    have ha : a=(1/1000 : ℝ) := by norm_num [a]
    rw [ha] at hlog ⊢
    linarith only [hlog]
  obtain ⟨hT,hpay⟩ := of_decide_eq_true hbudget
  have hTr : (0 : ℝ) ≤ T := by exact_mod_cast hT
  have hb : (T : ℝ)*(22/7) < -9/1000+B-1/(2*Y) := by
    have hr : ((T*(22/7) : ℚ) : ℝ) <
        ((-9/1000+FastArmCoverIntegral.payment cs-1/2048 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hpay
    norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_add,
      Rat.cast_one,Rat.cast_ofNat,Rat.cast_neg] at hr
    convert hr using 1
    norm_num [B,Y]
  have hpi : Real.pi < (22/7 : ℝ) := lt_trans Real.pi_lt_d4 (by norm_num)
  have hraw : (T : ℝ)*Real.pi < a*(Real.log (2*a/5)-1)+B-1/(2*Y) := by
    have hprod := mul_le_mul_of_nonneg_left hpi.le hTr
    linarith only [hprod,ho,hb]
  exact lt_of_lt_of_le ((lt_div_iff₀ Real.pi_pos).mpr hraw) hnorm

#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.PaidFixedClassIntegral
