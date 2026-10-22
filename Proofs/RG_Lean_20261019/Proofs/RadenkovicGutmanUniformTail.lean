/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanUniformTailPolynomials
import Proofs.RadenkovicGutmanScaledQuotient

namespace Gebendorfer.RadenkovicGutman.UniformTail
open Focus UniformTailPolynomials
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem disk_rectangle (d y : ℝ) (hd : 1 ≤ d) (hy : 1 ≤ y)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) : ζ.re ≤ 3/2 ∧ y ≤ ζ.im := by
  have hyp : 0<y := by linarith
  have hdp : 0<d := by linarith
  have hrx : ζ.re-(g d y).re ≤ r d y := by
    simpa only [Complex.sub_re] using (Complex.re_le_norm (ζ-g d y)).trans hζ
  have hiy : (g d y).im-ζ.im ≤ r d y := by
    have hn : ‖g d y-ζ‖ ≤ r d y := by simpa only [norm_sub_rev] using hζ
    simpa only [Complex.sub_im] using (Complex.im_le_norm (g d y-ζ)).trans hn
  simp [g,r,-Complex.ofReal_mul,-Complex.ofReal_div] at hrx hiy
  have hf : d/(2*y) ≤ d/2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [mul_nonneg hdp.le (sub_nonneg.mpr hy)]
  constructor <;> linarith

theorem norm_difference (y P Q : ℝ) (ζ : ℂ) :
    (1+y^2)*Complex.normSq (A P Q*ζ+N₀ y P Q)-
      y^2*Complex.normSq (B y P Q*ζ+D₀ y P Q)=
      C y P Q*(ζ.re^2+ζ.im^2)+H y P Q*ζ.re+L y P Q*ζ.im+E y P Q := by
  simp only [A,N₀,B,D₀,z,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat]
  dsimp [C,H,L,E]
  ring

theorem norm_difference_nonneg (y a b : ℝ) (hy : 1 ≤ y)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hx : ζ.re ≤ 3/2) (hv : y ≤ ζ.im) :
    0 ≤ (1+y^2)*Complex.normSq (A (y+a/y) (y+b/y)*ζ+N₀ y (y+a/y) (y+b/y))-
      y^2*Complex.normSq (B y (y+a/y) (y+b/y)*ζ+D₀ y (y+a/y) (y+b/y)) := by
  rw [norm_difference]
  have hc := C_nonneg y a b hy ha hb
  have hr := decreasing_nonneg y a b hy ha hb
  have hi := increasing_nonneg y a b hy ha hb
  have hcorner := corner_nonneg y a b hy ha hb
  have hs1 : 0 ≤ 3/2-ζ.re := sub_nonneg.mpr hx
  have hs2 : 0 ≤ ζ.im-y := sub_nonneg.mpr hv
  have he : C y (y+a/y) (y+b/y)*(ζ.re^2+ζ.im^2)+
      H y (y+a/y) (y+b/y)*ζ.re+L y (y+a/y) (y+b/y)*ζ.im+E y (y+a/y) (y+b/y)=
      corner y (y+a/y) (y+b/y)+C y (y+a/y) (y+b/y)*((3/2-ζ.re)^2+(ζ.im-y)^2)+
      decreasing y (y+a/y) (y+b/y)*(3/2-ζ.re)+
      increasing y (y+a/y) (y+b/y)*(ζ.im-y) := by
    dsimp [corner,decreasing,increasing]
    ring
  rw [he]
  exact add_nonneg (add_nonneg (add_nonneg hcorner
    (mul_nonneg hc (add_nonneg (sq_nonneg _) (sq_nonneg _))))
    (mul_nonneg hr hs1)) (mul_nonneg hi hs2)

theorem actual_log_lower (d y a b : ℝ) (hd : 1 ≤ d) (hy : 1 ≤ y)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    -1/(2*y^2) ≤ Real.log ‖quotient y (y+a/y) (y+b/y) ζ‖ := by
  have hyp : 0<y := by linarith
  have hdp : 0<d := by linarith
  have hPa : y ≤ y+a/y := by have := div_nonneg ha.1 hyp.le; linarith
  have hQb : y ≤ y+b/y := by have := div_nonneg hb.1 hyp.le; linarith
  have hden := denominator_nonzero d y (y+a/y) (y+b/y) hdp hyp hPa hQb ζ hζ
  have hdenp := Complex.normSq_pos.mpr hden
  obtain ⟨hx,hv⟩ := disk_rectangle d y hd hy ζ hζ
  have hf := norm_difference_nonneg y a b hy ha hb ζ hx hv
  have hs : y^2 ≤ (1+y^2)*Complex.normSq (quotient y (y+a/y) (y+b/y) ζ) := by
    rw [quotient,Complex.normSq_div,← mul_div_assoc]
    apply (le_div_iff₀ hdenp).mpr
    linarith
  rw [Complex.normSq_eq_norm_sq] at hs
  have hqp : 0<‖quotient y (y+a/y) (y+b/y) ζ‖ := by
    have hn := norm_nonneg (quotient y (y+a/y) (y+b/y) ζ)
    by_contra h
    have hz : ‖quotient y (y+a/y) (y+b/y) ζ‖=0 := by linarith
    rw [hz] at hs
    nlinarith
  have hratio : 1/‖quotient y (y+a/y) (y+b/y) ζ‖^2 ≤ (1+y^2)/y^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hqp) (sq_pos_of_pos hyp)).mpr
    simpa only [one_mul] using hs
  have he : (1+y^2)/y^2=1+1/y^2 := by field_simp; ring
  rw [he] at hratio
  have hl := Real.log_le_sub_one_of_pos
    (by positivity : 0<(1:ℝ)/‖quotient y (y+a/y) (y+b/y) ζ‖^2)
  rw [one_div,Real.log_inv,Real.log_pow] at hl
  have ht : (-1:ℝ)/(2*y^2)=-(1/y^2)/2 := by field_simp
  rw [ht]
  simp only [one_div] at hratio
  norm_num at hl
  simp only [one_div]
  linarith

#print axioms disk_rectangle
#print axioms norm_difference
#print axioms norm_difference_nonneg
#print axioms actual_log_lower
end
end Gebendorfer.RadenkovicGutman.UniformTail
