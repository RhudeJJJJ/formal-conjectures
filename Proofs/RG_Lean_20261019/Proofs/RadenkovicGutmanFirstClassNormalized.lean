/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFirstClassIntegral
import Proofs.RadenkovicGutmanFirstClassEscapeIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! The complete original 189/5000 reserve for physical arms one/one.
All finite rooted cores of degree one are included. The other fourteen arm
classes, hence the complete degreeOneLarge input, remain separate. -/
namespace Gebendorfer.RadenkovicGutman.FirstClassNormalized
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def finitePayment : ℚ := 3354807096003580173625700869/134722032206546673478926336000
def escapePayment : ℚ := 344921313615562164793601/3323734347200987010170880
theorem origin_log_checked : RationalLog.accepts (1/6250000) (-8) 23 32=true := by decide +kernel
theorem budget_checked : (decide ((189/5000 : ℚ)*(22/7) <
    -9/1000+finitePayment+escapePayment-1/2048))=true := by decide +kernel
noncomputable section
open Set MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical

theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u=1) :
    (189/5000 : ℝ) < normalizedIntegral C u 0 0 2 := by
  let a : ℝ := ((1/1000 : ℚ) : ℝ)
  let b : ℝ := ((8 : ℚ) : ℝ)
  let Y : ℝ := ((1024 : ℚ) : ℝ)
  let B : ℝ := ((finitePayment+escapePayment : ℚ) : ℝ)
  let f := MixedGraphIntegral.logarithm (source C u 0 0) (fused C u 0 0) 2
  have h₁ := FirstClassIntegral.actual_finite_payment C u hd
  have h₂ := FirstClassEscapeIntegral.actual_finite_payment C u hd
  change (finitePayment : ℝ) ≤ ∫ y : ℝ in a..b, f y at h₁
  change (escapePayment : ℝ) ≤ ∫ y : ℝ in b..Y, f y at h₂
  have hf := logarithm_integrable C u 0 0 2
  have hab : IntervalIntegrable f volume a b :=
    TailIntegral.interval_integrable_of_Ioi hf (by norm_num [a]) (by norm_num [a,b])
  have hbY : IntervalIntegrable f volume b Y :=
    TailIntegral.interval_integrable_of_Ioi hf (by norm_num [b]) (by norm_num [b,Y])
  have hadd := intervalIntegral.integral_add_adjacent_intervals hab hbY
  have hB : B ≤ ∫ y : ℝ in a..Y, f y := by
    dsimp only [B]
    rw [Rat.cast_add]
    linarith only [h₁,h₂,hadd]
  have hnorm := ClassGraphRemainders.normalized_lower_of_finite_payment C u 0 0
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
    have hr : (189/5000 : ℝ)*(22/7) <
        -9/1000+(finitePayment : ℝ)+(escapePayment : ℝ)-1/2048 := by
      norm_num [finitePayment,escapePayment]
    convert hr using 1
    norm_num [B,Y]
    ring
  have hpi : Real.pi < (22/7 : ℝ) := lt_trans Real.pi_lt_d4 (by norm_num)
  have hraw : (189/5000 : ℝ)*Real.pi < a*(Real.log (2*a/5)-1)+B-1/(2*Y) := by
    nlinarith only [ho,hb,hpi]
  exact lt_of_lt_of_le ((lt_div_iff₀ Real.pi_pos).mpr hraw) hnorm

#print axioms origin_log_checked
#print axioms budget_checked
#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.FirstClassNormalized
