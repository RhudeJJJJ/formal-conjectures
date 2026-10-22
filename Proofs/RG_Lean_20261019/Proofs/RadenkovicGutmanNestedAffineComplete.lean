/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedAffine

namespace Gebendorfer.RadenkovicGutman.NestedAffine
open NestedHorner Polynomial
noncomputable section
set_option maxHeartbeats 0

theorem coefficients_zero_of_parameter_zero {n : ℕ} (p : Poly (n+1))
    (h : ∀ x : Fin n → ℝ, parameterPolynomial p x=0) :
    ∀ c ∈ p, ∀ x : Fin n → ℝ, eval c x=0 := by
  induction p with
  | nil => simp
  | cons c p ih =>
    have hc (x : Fin n → ℝ) : eval c x=0 := by
      have hh := congrArg (fun P : ℝ[X] => P.coeff 0) (h x)
      simpa [parameterPolynomial] using hh
    have hp (x : Fin n → ℝ) : parameterPolynomial p x=0 := by
      have hh : (Polynomial.X : ℝ[X])*parameterPolynomial p x=0 := by
        simpa only [parameterPolynomial,hc,Polynomial.C_0,zero_add] using h x
      exact (mul_eq_zero.mp hh).resolve_left Polynomial.X_ne_zero
    intro a ha x
    rcases List.mem_cons.mp ha with he | he
    · subst a
      exact hc x
    · exact ih hp a he x

/-- Exact vanishing is complete even when nested lists retain zero padding. -/
theorem zeroCheck_complete (n : ℕ) (p : Poly n) (h : ∀ x, eval p x=0) :
    zeroCheck n p=true := by
  induction n with
  | zero =>
    apply decide_eq_true
    have hh : (p : ℝ)=0 := h (fun i => Fin.elim0 i)
    exact_mod_cast hh
  | succ n ih =>
    have hp (x : Fin n → ℝ) : parameterPolynomial p x=0 := by
      apply Polynomial.funext
      intro t
      rw [parameterPolynomial_eval,Polynomial.eval_zero]
      exact h _
    have hc := coefficients_zero_of_parameter_zero p hp
    simp only [zeroCheck,List.all_eq_true]
    intro c hm
    exact ih c (hc c hm)

/-- A proved integer substitution identity can discharge the rational checker
without evaluating the rational substitution separately in every leaf. -/
theorem check_complete (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ)
    (h : ∀ x, eval a x=eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i)) :
    check n p a l w=true := by
  apply zeroCheck_complete
  intro x
  rw [eval_add,eval_scale,transform_sound,← h x]
  norm_num

#print axioms zeroCheck_complete
#print axioms check_complete
end
end Gebendorfer.RadenkovicGutman.NestedAffine
