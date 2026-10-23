/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Gebendorfer.RadenkovicGutman.LogPolynomialLower

open Set
noncomputable section

def lowerFour (x : ℝ) : ℝ := x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4
def remainder (x : ℝ) : ℝ := Real.log (1 + x) - lowerFour x

theorem remainder_derivative (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt remainder (x ^ 4 / (1 + x)) x := by
  have hl := ((hasDerivAt_id x).const_add 1).log (show 1 + x ≠ 0 by linarith)
  have hp := ((((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
    (((hasDerivAt_id x).pow 3).div_const 3)).sub
    (((hasDerivAt_id x).pow 4).div_const 4))
  convert hl.sub hp using 1 <;> dsimp [remainder, lowerFour] <;>
    field_simp [show 1 + x ≠ 0 by linarith] <;> ring

/-- The fourth alternating polynomial is a lower bound on the whole positive ray. -/
theorem logarithm_lower_four (x : ℝ) (hx : 0 ≤ x) :
    lowerFour x ≤ Real.log (1 + x) := by
  have hc : ContinuousOn remainder (Ici 0) :=
    fun y hy => (remainder_derivative y hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn remainder (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc
      (fun y hy => (remainder_derivative y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy0 : 0 ≤ y := interior_subset hy
        exact div_nonneg (by positivity) (by linarith))
  have h := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx hx
  have hz : remainder 0 = 0 := by simp [remainder, lowerFour]
  rw [hz] at h
  exact sub_nonneg.mp h

theorem scaled_logarithm_lower (L c : ℝ) (hc : 0 < c) (hL : c ≤ L) :
    Real.log c + lowerFour (L / c - 1) ≤ Real.log L := by
  have hL0 : 0 < L := hc.trans_le hL
  have hd : 0 ≤ L / c - 1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hc).mpr
    simpa using hL
  have h := logarithm_lower_four (L / c - 1) hd
  rw [show 1 + (L / c - 1) = L / c by ring,
    Real.log_div hL0.ne' hc.ne'] at h
  linarith

theorem norm_logarithm_lower (q L c R : ℝ) (hc : 0 < c) (hL : c ≤ L)
    (hR : R ≤ Real.log c / 2) (hbound : L ≤ q ^ 2) :
    R + lowerFour (L / c - 1) / 2 ≤ Real.log q := by
  have hL0 : 0 < L := hc.trans_le hL
  have hlog := Real.log_le_log hL0 hbound
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hl := scaled_logarithm_lower L c hc hL
  linarith

/-- A checked rational constant plus an integrable polynomial payment. -/
theorem rational_payment_lower (q L : ℝ) (c R : ℚ) (k n : ℕ)
    (hc : 0 < c) (hL : (c : ℝ) ≤ L)
    (hlog : RationalLog.accepts c R k n = true) (hbound : L ≤ q ^ 2) :
    (R : ℝ) + lowerFour (L / (c : ℝ) - 1) / 2 ≤ Real.log q :=
  norm_logarithm_lower q L c R (by exact_mod_cast hc) hL
    (RationalLog.sound c R k n hlog) hbound

#print axioms remainder_derivative
#print axioms logarithm_lower_four
#print axioms scaled_logarithm_lower
#print axioms norm_logarithm_lower
#print axioms rational_payment_lower

end
end Gebendorfer.RadenkovicGutman.LogPolynomialLower
