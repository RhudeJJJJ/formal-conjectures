/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLongArmBothPolynomials
import Proofs.RadenkovicGutmanLongArmBothGeometry
namespace Gebendorfer.RadenkovicGutman.DegreeInterpolation
open Focus CoreQuotient LongArmBothFamily
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
def blend (f : ℝ → ℝ) (d : ℝ) : ℝ :=
  (d-2)*(d-3)*(d-4)*(d-5)/120*f 0
  - d*(d-3)*(d-4)*(d-5)/12*f 2
  + d*(d-2)*(d-4)*(d-5)/6*f 3
  - d*(d-2)*(d-3)*(d-5)/8*f 4
  + d*(d-2)*(d-3)*(d-4)/30*f 5

theorem horner (a b c e f d : ℝ) :
    a+d*(b+d*(c+d*(e+d*f))) = blend (fun x => a+x*(b+x*(c+x*(e+x*f)))) d := by
  unfold blend
  ring
#print axioms horner

theorem eval_list {n : ℕ} (a b c e f : NestedHorner.Poly n) (x : Fin n → ℝ) (d : ℝ) :
    NestedHorner.eval [a,b,c,e,f] (Fin.cons d x) =
    blend (fun z => NestedHorner.eval [a,b,c,e,f] (Fin.cons z x)) d := by
  simpa only [NestedHorner.eval_cons, NestedHorner.eval_nil, Fin.cons_zero, Fin.cons_succ, mul_zero, add_zero] using
    horner (NestedHorner.eval a x) (NestedHorner.eval b x) (NestedHorner.eval c x) (NestedHorner.eval e x) (NestedHorner.eval f x) d
#print axioms eval_list
theorem poly_U (d y v t : ℝ) : up d y v t = blend (fun z => up z y v t) d := by
  unfold up
  change NestedHorner.eval _ (Fin.cons d ![v,t,y^2]) = _
  exact eval_list _ _ _ _ _ _ _
#print axioms poly_U
theorem poly_J (d y v t : ℝ) : jp d y v t = blend (fun z => jp z y v t) d := by
  unfold jp
  change NestedHorner.eval _ (Fin.cons d ![v,t,y^2]) = _
  exact eval_list _ _ _ _ _ _ _
#print axioms poly_J
def lhsU (d y p q : ℝ) : ℝ := Complex.normSq (b d y p q * star (e d y p q) - a d p q * star (c d y p q))
theorem lhs_U (d y p q : ℝ) : lhsU d y p q = blend (fun z => lhsU z y p q) d := by
  unfold blend lhsU b a c e g
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring
#print axioms lhs_U
def lhsJ (d y p q : ℝ) : ℝ := (Complex.normSq (b d y p q) - Complex.normSq (a d p q))^2
theorem lhs_J (d y p q : ℝ) : lhsJ d y p q = blend (fun z => lhsJ z y p q) d := by
  unfold blend lhsJ b a g
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring
#print axioms lhs_J
end
end Gebendorfer.RadenkovicGutman.DegreeInterpolation
