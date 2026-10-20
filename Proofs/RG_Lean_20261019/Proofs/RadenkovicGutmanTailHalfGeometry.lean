/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailHalfPolynomial

/-! Exact affine half-plane test for the same finite Weyl disk and the
original infinite-core tail envelope. Polynomial signs are separate inputs. -/
namespace Gebendorfer.RadenkovicGutman.TailHalfGeometry
open Focus TailHalfPolynomial LargeDegreeReserve
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def xCoeff (y P Q : ℝ) : ℝ := 2*(Complex.normSq (B y P Q)*(A P Q*star (N₀ y P Q)).re-Complex.normSq (A P Q)*(B y P Q*star (D₀ y P Q)).re)
def tCoeff (y P Q : ℝ) : ℝ := -2*(Complex.normSq (B y P Q)*(A P Q*star (N₀ y P Q)).im-Complex.normSq (A P Q)*(B y P Q*star (D₀ y P Q)).im)
def cCoeff (y P Q : ℝ) : ℝ := Complex.normSq (B y P Q)*Complex.normSq (N₀ y P Q)-Complex.normSq (A P Q)*Complex.normSq (D₀ y P Q)
def centerValue (d y P Q : ℝ) : ℝ := xCoeff y P Q*(2-d)+tCoeff y P Q*(y+d/(2*y))+cCoeff y P Q
def squareMargin (d y P Q : ℝ) : ℝ := (centerValue d y P Q)^2-(r d y)^2*((xCoeff y P Q)^2+(tCoeff y P Q)^2)

theorem affine_identity (y P Q : ℝ) (ζ : ℂ) :
    Complex.normSq (B y P Q)*Complex.normSq (A P Q*ζ+N₀ y P Q)-
      Complex.normSq (A P Q)*Complex.normSq (B y P Q*ζ+D₀ y P Q) =
        xCoeff y P Q*ζ.re+tCoeff y P Q*ζ.im+cCoeff y P Q := by
  simp only [xCoeff,tCoeff,cCoeff,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem denominator_ne_zero (d y P Q : ℝ) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    B y P Q*ζ+D₀ y P Q ≠ 0 := by
  have hi := Complex.im_le_norm (g d y-ζ)
  rw [norm_sub_rev] at hi
  have him : 0 < ζ.im := by
    simp only [g,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero,Complex.sub_im] at hi
    unfold r g at hζ
    linarith
  intro hz
  have he : ζ = -D₀ y P Q/B y P Q := by
    apply (eq_div_iff (B_ne_zero y P Q hy hP hQ)).mpr
    linear_combination hz
  have hp := denominator_pole_im y P Q hy hP hQ
  rw [← he] at hp
  linarith

theorem ratio_lower_of_margins (d y P Q : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q)
    (hV : 0 ≤ centerValue d y P Q) (hK : 0 ≤ squareMargin d y P Q)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    Complex.normSq (A P Q)/Complex.normSq (B y P Q) ≤ ‖quotient y P Q ζ‖^2 := by
  let X := xCoeff y P Q
  let T := tCoeff y P Q
  let V := centerValue d y P Q
  let dx := ζ.re-(g d y).re
  let dy := ζ.im-(g d y).im
  have hr : 0 ≤ r d y := by unfold r; positivity
  have hn : dx^2+dy^2 ≤ (r d y)^2 := by
    have h : ‖ζ-g d y‖^2 ≤ (r d y)^2 := by nlinarith [norm_nonneg (ζ-g d y)]
    rw [← Complex.normSq_eq_norm_sq] at h
    simpa only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,dx,dy,pow_two] using h
  have hc : (X*dx+T*dy)^2 ≤ (X^2+T^2)*(dx^2+dy^2) := by
    nlinarith [sq_nonneg (X*dy-T*dx)]
  have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ X^2+T^2 by positivity)
  have hs : (X*dx+T*dy)^2 ≤ V^2 := by
    change 0 ≤ V^2-(r d y)^2*(X^2+T^2) at hK
    nlinarith only [hc,hm,hK]
  have habs : |X*dx+T*dy| ≤ V :=
    (sq_le_sq₀ (abs_nonneg _) hV).mp (by simpa using hs)
  have ha := (abs_le.mp habs).1
  have he : xCoeff y P Q*ζ.re+tCoeff y P Q*ζ.im+cCoeff y P Q = V+(X*dx+T*dy) := by
    dsimp [V,X,T,dx,dy,centerValue,g]
    simp only [Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im]
    ring
  have hH : 0 ≤ Complex.normSq (B y P Q)*Complex.normSq (A P Q*ζ+N₀ y P Q)-
      Complex.normSq (A P Q)*Complex.normSq (B y P Q*ζ+D₀ y P Q) := by
    rw [affine_identity,he]
    linarith only [ha]
  have hb := Complex.normSq_pos.mpr (B_ne_zero y P Q hy hP hQ)
  have hden := norm_pos_iff.mpr (denominator_ne_zero d y P Q hy hP hQ ζ hζ)
  rw [quotient,norm_div,div_pow]
  apply (div_le_div_iff₀ hb (sq_pos_of_pos hden)).mpr
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  nlinarith only [hH]

theorem infinity_ratio_lower (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    1/(1+(tailParameter y)^2) ≤ Complex.normSq (A P Q)/Complex.normSq (B y P Q) := by
  let t := tailParameter y
  obtain ⟨ht,_,hq⟩ := tail_parameter_properties y hy.le
  have hf (s : ℝ) : 2*s-y ≤ t*(1+s^2) := by
    have he : t*(t*(1+s^2)-(2*s-y)) = (t*s-1)^2 := by
      nlinarith only [hq]
    have hn : 0 ≤ t*(t*(1+s^2)-(2*s-y)) := by rw [he]; positivity
    have h := nonneg_of_mul_nonneg_right hn ht
    linarith only [h]
  have hm := mul_le_mul (hf P) (hf Q) (by linarith : 0 ≤ 2*Q-y) (by positivity : 0 ≤ t*(1+P^2))
  have ha : Complex.normSq (A P Q) = (1+P^2)*(1+Q^2) := by
    simp [A,Complex.normSq_apply]; ring
  have hb : Complex.normSq (B y P Q) = Complex.normSq (A P Q)+(2*P-y)*(2*Q-y) := by
    simp [A,B,Complex.normSq_apply]; ring
  apply (div_le_div_iff₀ (by positivity : 0 < 1+t^2)
    (Complex.normSq_pos.mpr (B_ne_zero y P Q hy hP hQ))).mpr
  simp only [hb,ha]
  nlinarith only [hm]

theorem infinity_ratio_ge_half (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    (1/2 : ℝ) ≤ Complex.normSq (A P Q)/Complex.normSq (B y P Q) := by
  obtain ⟨ht,ht1,_⟩ := tail_parameter_properties y hy.le
  have hs : (tailParameter y)^2 ≤ 1 := by simpa using pow_le_pow_left₀ ht.le ht1 2
  have hh : (1/2 : ℝ) ≤ 1/(1+(tailParameter y)^2) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < 1+(tailParameter y)^2)).mpr
    nlinarith only [hs]
  exact hh.trans (infinity_ratio_lower y P Q hy hP hQ)

/-- The original tangent low-strip leading coefficient is strictly positive
by the infinity envelope, for every actual arm interval and 0<=c<=1/2. -/
theorem tangent_lead_pos (y P Q c : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q)
    (hc : c ∈ Set.Icc (0 : ℝ) (1/2)) :
    0 < Complex.normSq (A P Q)-(c^2/4)*Complex.normSq (B y P Q) := by
  have hb := Complex.normSq_pos.mpr (B_ne_zero y P Q hy hP hQ)
  have hh := (le_div_iff₀ hb).mp (infinity_ratio_ge_half y P Q hy hP hQ)
  have hs : c^2/4 ≤ (1/16 : ℝ) := by
    nlinarith only [pow_le_pow_left₀ hc.1 hc.2 2]
  have hm := mul_le_mul_of_nonneg_right hs hb.le
  nlinarith only [hh,hm,hb]

theorem log_lower_of_margins (d y P Q : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q)
    (hV : 0 ≤ centerValue d y P Q) (hK : 0 ≤ squareMargin d y P Q)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    TailIntegral.phi y ≤ Real.log ‖quotient y P Q ζ‖ := by
  have hs := (infinity_ratio_lower y P Q hy hP hQ).trans
    (ratio_lower_of_margins d y P Q hd hy hP hQ hV hK ζ hζ)
  have hl := Real.log_le_log (by positivity : 0 < 1/(1+(tailParameter y)^2)) hs
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity : 1+(tailParameter y)^2 ≠ 0),
    Real.log_one,zero_sub,Real.log_pow] at hl
  norm_num at hl
  unfold TailIntegral.phi TailIntegral.positiveTail
  linarith only [hl]

#print axioms affine_identity
#print axioms denominator_ne_zero
#print axioms ratio_lower_of_margins
#print axioms infinity_ratio_lower
#print axioms infinity_ratio_ge_half
#print axioms tangent_lead_pos
#print axioms log_lower_of_margins
end
end Gebendorfer.RadenkovicGutman.TailHalfGeometry
