/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalComplexPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Gebendorfer.RadenkovicGutman.RationalPolynomialIntegral

open Polynomial PolynomialPathMap RationalComplexPolynomial MeasureTheory
noncomputable section

theorem derivative_evaluation (p : ℚ[X]) (x : ℝ) :
    HasDerivAt (fun y => realEvaluator y p) (realEvaluator x p.derivative) x := by
  simpa [realEvaluator, Polynomial.aeval_def] using p.hasDerivAt_aeval x

theorem evaluation_continuous (p : ℚ[X]) : Continuous (fun y => realEvaluator y p) :=
  continuous_iff_continuousAt.mpr (fun y => (derivative_evaluation p y).continuousAt)

theorem rational_evaluation (p : ℚ[X]) (x : ℚ) :
    realEvaluator (x : ℝ) p = (p.eval x : ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, Polynomial.eval_add, Rat.cast_add, hp, hq]
  | monomial n c => simp [realEvaluator]

def accepts (p F : List ℚ) (a b L : ℚ) : Bool :=
  decide ((ofList F).derivative = ofList p ∧ (ofList F).eval b - (ofList F).eval a = L)

/-- The exact rational primitive is checked before any integral payment is used. -/
theorem sound (p F : List ℚ) (a b L : ℚ) (hcheck : accepts p F a b L = true) :
    (∫ y : ℝ in (a : ℝ)..(b : ℝ), realEvaluator y (ofList p)) = (L : ℝ) := by
  obtain ⟨hd,he⟩ := of_decide_eq_true hcheck
  have hF (y : ℝ) : HasDerivAt (fun t => realEvaluator t (ofList F))
      (realEvaluator y (ofList p)) y := by
    have h := derivative_evaluation (ofList F) y
    rw [hd] at h
    exact h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y)
    ((evaluation_continuous (ofList p)).intervalIntegrable (a : ℝ) (b : ℝ))
  rw [rational_evaluation, rational_evaluation, ← Rat.cast_sub, he] at h
  exact h

theorem control : accepts [1,1] [0,1,1/2] 0 1 (3/2) = true := by
  rw [accepts, decide_eq_true_eq]
  constructor
  · apply Polynomial.funext
    intro t
    norm_num [ofList]
    ring
  · norm_num [ofList]
theorem rejects_wrong_payment : accepts [1,1] [0,1,1/2] 0 1 2 = false := by
  rw [accepts, decide_eq_false_iff_not]
  rintro ⟨_, h⟩
  norm_num [ofList] at h

#print axioms derivative_evaluation
#print axioms evaluation_continuous
#print axioms rational_evaluation
#print axioms sound
#print axioms control
#print axioms rejects_wrong_payment

end
end Gebendorfer.RadenkovicGutman.RationalPolynomialIntegral
