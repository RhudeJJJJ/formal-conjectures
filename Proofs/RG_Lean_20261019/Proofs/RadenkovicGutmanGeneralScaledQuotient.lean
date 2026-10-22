/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralGraphQuotient
import Proofs.RadenkovicGutmanBernstein

/-! A rotation of the degree-one Schur disk removes every reciprocal ordinate
from its four scaled coefficients, including at the actual mean shifts. -/
namespace Gebendorfer.RadenkovicGutman.GeneralScaledQuotient
open GeneralGraphQuotient CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

def scale (y : ℝ) : ℂ := (2*y : ℝ)*Complex.I
def centerPolynomial (x : ℝ) (w : ℂ) : ℂ :=
  2*w*(x-1)+2*w^2-1
def parameter (x y : ℝ) (ζ : ℂ) : ℂ := scale y*(ζ-center x y 1)
def a (x y : ℝ) (p q : ℕ) : ℂ := numeratorCoefficient (point x y) p q
def b (x y : ℝ) (p q : ℕ) : ℂ :=
  a x y p q*centerPolynomial x ((y : ℂ)*Complex.I)-scale y*sourceConstant (point x y) p q
def c (x y : ℝ) (p q : ℕ) : ℂ := denominatorCoefficient (point x y) p q
def e (x y : ℝ) (p q : ℕ) : ℂ :=
  c x y p q*centerPolynomial x ((y : ℂ)*Complex.I)-scale y*fusedConstant (point x y) p q

theorem scale_ne_zero (y : ℝ) (hy : 0 < y) : scale y ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero

theorem center_identity (x y : ℝ) (hy : 0 < y) :
    centerPolynomial x ((y : ℂ)*Complex.I)=scale y*center x y 1 := by
  apply Complex.ext <;>
    simp only [centerPolynomial,scale,center,pow_two,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,Complex.one_im] <;>
    field_simp [hy.ne'] <;> ring

theorem parameter_norm (x y : ℝ) (hy : 0 < y) (ζ : ℂ)
    (hζ : ‖ζ-center x y 1‖ ≤ 1/(2*y)) : ‖parameter x y ζ‖ ≤ 1 := by
  have hp : 0 < 2*y := by positivity
  have hs : ‖scale y‖=2*y := by
    unfold scale
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  rw [parameter,norm_mul,hs]
  calc
    (2*y)*‖ζ-center x y 1‖ ≤ (2*y)*(1/(2*y)) :=
      mul_le_mul_of_nonneg_left hζ hp.le
    _ = 1 := by field_simp

theorem scaled_quotient (x y : ℝ) (hy : 0 < y) (p q : ℕ) (ζ : ℂ) :
    quotient (point x y) p q ζ=
      (a x y p q*parameter x y ζ+b x y p q)/
        (c x y p q*parameter x y ζ+e x y p q) := by
  have h (A B : ℂ) :
      A*parameter x y ζ+(A*centerPolynomial x ((y : ℂ)*Complex.I)-scale y*B)=
        scale y*(A*ζ-B) := by
    rw [center_identity x y hy]
    unfold parameter
    ring
  unfold b e
  rw [h,h,mul_div_mul_left _ _ (scale_ne_zero y hy)]
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact coefficient and separation checks imply the norm bound on the actual
Laplacian quotient of every degree-one core. -/
theorem actual_norm_certificate (C : SimpleGraph V) (u : V) (hd : C.degree u=1)
    (x y : ℝ) (hy : 0 < y) (p q : ℕ) (s L : ℝ) (hs : 0 < s)
    (hE : 0 < Complex.normSq (e x y p q)-Complex.normSq (c x y p q))
    (hN : 0 < Complex.normSq (b x y p q)-Complex.normSq (a x y p q))
    (hL : L*((1+s)*‖b x y p q*star (e x y p q)-a x y p q*star (c x y p q)‖^2+
      (1+1/s)*‖a x y p q*e x y p q-b x y p q*c x y p q‖^2) ≤
        (Complex.normSq (b x y p q)-Complex.normSq (a x y p q))^2) :
    L ≤ ‖(shifted (point x y) (source C u p q)).det/
      (shifted (point x y) (fused C u p q)).det‖^2 := by
  have hζ := actual_disk C u x y hy
  rw [hd] at hζ
  norm_num only [Nat.cast_one] at hζ
  rw [actual_quotient C u (point x y) (by simpa [point] using hy) p q,
    scaled_quotient x y hy p q]
  exact Bernstein.mobius_certificate _ _ _ _ _ hE hN
    (parameter_norm x y hy _ hζ) s L hs hL

#print axioms scale_ne_zero
#print axioms center_identity
#print axioms parameter_norm
#print axioms scaled_quotient
#print axioms actual_norm_certificate
end
end Gebendorfer.RadenkovicGutman.GeneralScaledQuotient
