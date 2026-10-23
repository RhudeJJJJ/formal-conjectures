/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualMeanOrigin
import Proofs.RadenkovicGutmanRationalLog

namespace Gebendorfer.RadenkovicGutman.Mean16Origin
open CoreQuotient Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
def logEpsilon : ℚ := (-166355323334387/20000000000000)
def logReciprocalB : ℚ := (-277841403084977/100000000000000)
def payment : ℚ := (-72476126234807/3276800000000000000)
theorem epsilon_log_checked : RationalLog.accepts (1/16777216) logEpsilon 24 32 = true := by decide +kernel
theorem reciprocal_log_checked : RationalLog.accepts (1/259) logReciprocalB 9 32 = true := by decide +kernel

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+2 ≤ 16) :
    (payment : ℝ) ≤ ∫ y : ℝ in (0 : ℝ)..(1/16777216),
      MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (15/8) y := by
  have hε := RationalLog.sound (1/16777216) logEpsilon _ _ epsilon_log_checked
  have hB := RationalLog.sound (1/259) logReciprocalB _ _ reciprocal_log_checked
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hε hB
  rw [show Real.log (1/259 : ℝ) = -Real.log 259 by rw [one_div,Real.log_inv]] at hB
  have hp : (payment : ℝ) ≤ (16 : ℝ)*(1/16777216)*
      (Real.log (1/16777216)-Real.log 259-1) := by
    norm_num [payment,logEpsilon,logReciprocalB] at hε hB ⊢
    linarith only [hε,hB]
  have h := ActualMeanOrigin.actual_origin_lower G u 0 0 16 (by simpa using hN)
    (15/8) (1/16777216) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat,show (16 : ℝ)^2+3=259 by norm_num] at h
  rw [show (16 : ℝ)*(1/16777216)=1/1048576 by norm_num] at hp
  exact hp.trans h

#print axioms epsilon_log_checked
#print axioms reciprocal_log_checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.Mean16Origin
