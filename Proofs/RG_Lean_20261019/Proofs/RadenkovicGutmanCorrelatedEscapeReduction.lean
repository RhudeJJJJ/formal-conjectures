/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCorrelatedEscape

/-! Exact algebraic reductions before original escape denominator clearing.
Source: the original Focus coefficients, original correlated quadratic and
the same Schur disk. No coefficient, box or sign target is replaced. -/
namespace Gebendorfer.RadenkovicGutman.CorrelatedEscapeReduction
open Focus CorrelatedEscape
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false

def center (d y r : ℝ) : ℂ := (2-d : ℝ)+(y+r : ℝ)*Complex.I
def baseValue (a bx bt c y : ℝ) : ℝ := QuadraticDisk.value a bx bt c (z y)
def horizontal (a bx : ℝ) : ℝ := 4*a+bx
def vertical (a bt y : ℝ) : ℝ := 2*a*y+bt
def coreValue (a bx bt c d y : ℝ) : ℝ := baseValue a bx bt c y+a*d^2-d*horizontal a bx

theorem directed_translation (a bx bt c d y r : ℝ) :
    QuadraticDisk.directed a bx bt c r (center d y r) =
      4*a*(coreValue a bx bt c d y+r*vertical a bt y+2*a*r^2) := by
  simp only [QuadraticDisk.directed,QuadraticDisk.gradientSq,QuadraticDisk.value,
    coreValue,baseValue,horizontal,vertical,center,z,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem reserve_translation (a bx bt c d y r : ℝ) :
    QuadraticDisk.reserve a bx bt c r (center d y r) =
      16*a^2*((coreValue a bx bt c d y)^2+
        2*coreValue a bx bt c d y*r*vertical a bt y+
        r^2*(4*a*baseValue a bx bt c y-(horizontal a bx)^2)) := by
  unfold QuadraticDisk.reserve
  rw [directed_translation]
  simp only [QuadraticDisk.gradientSq,QuadraticDisk.value,coreValue,baseValue,
    horizontal,vertical,center,z,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

def errorWeight (t : ℝ) : ℝ := -t*(1-t/2+t^2/6)
def factorLead (y P Q t : ℝ) : ℝ :=
  errorWeight t*(1+P^2)*(1+Q^2)-(2*P-y)*(2*Q-y)
def factorBase (y P Q t : ℝ) : ℝ := errorWeight t*(4+y^2)*(P*Q+1)^2
def factorHorizontal (y P Q t : ℝ) : ℝ :=
  2*(P*Q+1)*(errorWeight t*(2*(P*Q-1)-y*(P+Q))-4-y^2)
def factorVertical (y P Q t : ℝ) : ℝ :=
  2*errorWeight t*(P*Q+1)*(y*(P*Q-1)+2*(P+Q))
def factorCore (d y P Q t : ℝ) : ℝ :=
  factorBase y P Q t+factorLead y P Q t*d^2-d*factorHorizontal y P Q t

theorem lead_factor (y P Q t : ℝ) : lead y P Q t=factorLead y P Q t := by
  simp only [lead,factorLead,errorWeight,cubic,quadratic,A,B,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  ring

theorem base_factor (y P Q t : ℝ) :
    baseValue (lead y P Q t) (bx y P Q t) (bt y P Q t) (constant y P Q t) y =
      factorBase y P Q t := by
  simp only [baseValue,QuadraticDisk.value,lead,bx,bt,constant,factorBase,
    errorWeight,cubic,quadratic,A,B,N₀,D₀,z,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem horizontal_factor (y P Q t : ℝ) :
    horizontal (lead y P Q t) (bx y P Q t)=factorHorizontal y P Q t := by
  simp only [horizontal,lead,bx,factorHorizontal,errorWeight,cubic,quadratic,
    A,B,N₀,D₀,z,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem vertical_factor (y P Q t : ℝ) :
    vertical (lead y P Q t) (bt y P Q t) y=factorVertical y P Q t := by
  simp only [vertical,lead,bt,factorVertical,errorWeight,cubic,quadratic,
    A,B,N₀,D₀,z,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem directed_reduced (d y P Q t : ℝ) : directed d y P Q t =
    4*factorLead y P Q t*(factorCore d y P Q t+r d y*factorVertical y P Q t+
      2*factorLead y P Q t*(r d y)^2) := by
  unfold directed
  change QuadraticDisk.directed _ _ _ _ _ (center d y (r d y)) = _
  rw [directed_translation]
  unfold coreValue
  simp only [base_factor,horizontal_factor,vertical_factor]
  simp only [lead_factor]
  rfl

theorem reserve_reduced (d y P Q t : ℝ) : reserve d y P Q t =
    16*(factorLead y P Q t)^2*((factorCore d y P Q t)^2+
      2*factorCore d y P Q t*r d y*factorVertical y P Q t+
      (r d y)^2*(4*factorLead y P Q t*factorBase y P Q t-(factorHorizontal y P Q t)^2)) := by
  unfold reserve
  change QuadraticDisk.reserve _ _ _ _ _ (center d y (r d y)) = _
  rw [reserve_translation]
  unfold coreValue
  simp only [base_factor,horizontal_factor,vertical_factor]
  simp only [lead_factor]
  rfl

theorem payment_reciprocal (h x : ℝ) (hh : h ≠ 0) :
    payment (1/h) x=(42/25 : ℝ)*h/(1+x^2) := by
  unfold payment
  field_simp [hh,show (1+x^2) ≠ 0 by positivity]

theorem radius_reciprocal (h x : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    r (1/h) (x/h)=1/(2*x) := by
  unfold r
  field_simp [hh,hx]

#print axioms directed_translation
#print axioms reserve_translation
#print axioms lead_factor
#print axioms base_factor
#print axioms horizontal_factor
#print axioms vertical_factor
#print axioms directed_reduced
#print axioms reserve_reduced
#print axioms payment_reciprocal
#print axioms radius_reciprocal
end
end Gebendorfer.RadenkovicGutman.CorrelatedEscapeReduction
