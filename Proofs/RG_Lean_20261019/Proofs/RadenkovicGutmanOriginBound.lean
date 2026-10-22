/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginHalfplane
import Proofs.RadenkovicGutmanScaledQuotient
namespace Gebendorfer.RadenkovicGutman.OriginBound
open Focus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem numerator_identity (y P Q : ℝ) (ζ : ℂ) :
    ((A P Q*ζ+N₀ y P Q)*star (z y-ζ)).im=
      (P*Q+1)*(y*(z y-ζ).re-2*(z y-ζ).im)+
        (P+Q)*Complex.normSq (z y-ζ) := by
  simp only [A,N₀,z,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem denominator_identity (y P Q : ℝ) (ζ : ℂ) :
    B y P Q*ζ+D₀ y P Q=(A P Q*ζ+N₀ y P Q)-z y*(z y-ζ) := by
  dsimp [A,N₀,B,D₀,z]
  push_cast
  ring

theorem numerator_norm (d y P Q : ℝ) (hd : 0 < d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    2*y*‖z y-ζ‖ ≤ ‖A P Q*ζ+N₀ y P Q‖ := by
  have hv := OriginHalfplane.linear_positive d y hd hy ζ hζ
  have hw : z y-ζ ≠ 0 := by
    intro hz
    rw [hz] at hv
    norm_num at hv
  have hwp : 0 < ‖z y-ζ‖ := norm_pos_iff.mpr hw
  have hp : 0 < P := hy.trans_le hP
  have hq : 0 < Q := hy.trans_le hQ
  have hr : 0 ≤ P*Q+1 := by positivity
  have him := Complex.im_le_norm ((A P Q*ζ+N₀ y P Q)*star (z y-ζ))
  rw [numerator_identity,norm_mul,norm_star,Complex.normSq_eq_norm_sq] at him
  apply (mul_le_mul_iff_right₀ hwp).mp
  have hs : 0 ≤ P+Q-2*y := by linarith
  nlinarith [mul_nonneg hr hv.le,mul_nonneg hs (sq_nonneg ‖z y-ζ‖)]

/-- A universal integrable origin bound, with no finite arm cutoff. -/
theorem norm_lower (d y P Q : ℝ) (hd : 0 < d) (hy : 0 < y) (hy1 : y ≤ 1)
    (hP : y ≤ P) (hQ : y ≤ Q) (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    2*y/5 ≤ ‖quotient y P Q ζ‖ := by
  have hn := numerator_norm d y P Q hd hy hP hQ ζ hζ
  have hzn : ‖z y‖^2=4+y^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [z,Complex.normSq_apply,pow_two]
  have hzb : ‖z y‖ ≤ 3 := by nlinarith [norm_nonneg (z y)]
  have htri : ‖B y P Q*ζ+D₀ y P Q‖ ≤
      ‖A P Q*ζ+N₀ y P Q‖+3*‖z y-ζ‖ := by
    rw [denominator_identity]
    have ht := norm_sub_le (A P Q*ζ+N₀ y P Q) (z y*(z y-ζ))
    rw [norm_mul] at ht
    have hm := mul_le_mul_of_nonneg_right hzb (norm_nonneg (z y-ζ))
    linarith
  have hden := denominator_nonzero d y P Q hd hy hP hQ ζ hζ
  rw [quotient,norm_div]
  apply (le_div_iff₀ (norm_pos_iff.mpr hden)).mpr
  have ht := mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ 2*y)
  have hn1 := mul_le_mul_of_nonneg_right hy1 (norm_nonneg (A P Q*ζ+N₀ y P Q))
  nlinarith

theorem logarithm_lower (d y P Q : ℝ) (hd : 0 < d) (hy : 0 < y) (hy1 : y ≤ 1)
    (hP : y ≤ P) (hQ : y ≤ Q) (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    Real.log (2*y/5) ≤ Real.log ‖quotient y P Q ζ‖ := by
  have hlow := norm_lower d y P Q hd hy hy1 hP hQ ζ hζ
  exact Real.log_le_log (by positivity) hlow

#print axioms numerator_identity
#print axioms denominator_identity
#print axioms numerator_norm
#print axioms norm_lower
#print axioms logarithm_lower
end
end Gebendorfer.RadenkovicGutman.OriginBound
