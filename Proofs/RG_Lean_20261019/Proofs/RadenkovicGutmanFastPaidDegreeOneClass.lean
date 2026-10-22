/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastCellPartition
import Mathlib.Analysis.Real.Pi.Bounds

namespace Gebendorfer.RadenkovicGutman.FastPaidDegreeOneClass
set_option maxHeartbeats 0

def accepts (P : ℚ) : Bool :=
  decide ((189/5000 : ℚ)*(22/7) < -9/1000+P-1/2048)

theorem origin_log_checked : RationalLog.accepts (1/6250000) (-8) 23 32=true := by decide +kernel

noncomputable section
open CoreQuotient Set MeasureTheory ActualFusionIntegral
open scoped Classical

theorem budget_sound (P : ℚ) (h : accepts P=true) :
    (189/5000 : ℝ)*(22/7) < -9/1000+(P : ℝ)-1/2048 := by
  have hg : (((189/5000 : ℚ)*(22/7) : ℚ) : ℝ) < ((-9/1000+P-1/2048 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (of_decide_eq_true h)
  norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_add,Rat.cast_one,
    Rat.cast_ofNat,Rat.cast_neg] at hg ⊢
  exact hg

/-- Any paid class partition closes the exact original large degree-one
reserve for all physical arms classified by that one fixed class pair. -/
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (cs : List FastCellPartition.Slice)
    (hcheck : FastCellPartition.checkAt 1 c₁ c₂ (1/1000) 1024 cs=true)
    (hbudget : accepts (FastCellPartition.payment cs)=true) :
    (189/5000 : ℝ) < normalizedIntegral C u p q 2 := by
  let a : ℝ := ((1/1000 : ℚ) : ℝ)
  let Y : ℝ := ((1024 : ℚ) : ℝ)
  let B : ℝ := (FastCellPartition.payment cs : ℝ)
  have hc : FastCellPartition.checkAt ((1 : ℕ) : ℚ) c₁ c₂ (1/1000) 1024 cs=true := by
    simpa only [Nat.cast_one] using hcheck
  have hB := FastCellPartition.integral_lower C u p q 1 (by decide) hd c₁ c₂ hp hq
    (1/1000) 1024 (by norm_num) cs hc
  have hnorm := ClassGraphRemainders.normalized_lower_of_finite_payment C u p q
    (by omega) a Y B (by norm_num [a]) (by norm_num [a]) (by norm_num [Y]) hB
  have hl := RationalLog.sound (1/6250000) (-8) 23 32 origin_log_checked
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
  have hb : (189/5000 : ℝ)*(22/7) < -9/1000+B-1/(2*Y) := by
    have hr := budget_sound _ hbudget
    convert hr using 1
    norm_num [B,Y]
  have hpi : Real.pi < (22/7 : ℝ) := lt_trans Real.pi_lt_d4 (by norm_num)
  have hraw : (189/5000 : ℝ)*Real.pi < a*(Real.log (2*a/5)-1)+B-1/(2*Y) := by
    nlinarith only [ho,hb,hpi]
  exact lt_of_lt_of_le ((lt_div_iff₀ Real.pi_pos).mpr hraw) hnorm

#print axioms origin_log_checked
#print axioms budget_sound
#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.FastPaidDegreeOneClass
