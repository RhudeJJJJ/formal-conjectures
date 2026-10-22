/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPolynomialPathMap

/-! Exact real and imaginary polynomial representatives of rational Horner
lists evaluated on the imaginary axis. No sampled identity is used. -/
namespace Gebendorfer.RadenkovicGutman.RationalComplexPolynomial
noncomputable section
open Polynomial PolynomialPathMap
set_option maxHeartbeats 0

def parts : List ℚ → ℚ[X] × ℚ[X]
  | [] => (0,0)
  | c :: p => (C c-X*(parts p).2,X*(parts p).1)

noncomputable def realEvaluator (y : ℝ) : ℚ[X] →+* ℝ :=
  Polynomial.eval₂RingHom (Rat.castHom ℝ) y

theorem complex_C (y : ℝ) (c : ℚ) : evaluator y (C c)=(c : ℂ) := by
  simp [evaluator]
theorem complex_X (y : ℝ) : evaluator y X=(y : ℂ)*Complex.I := by
  simp [evaluator]
theorem real_C (y : ℝ) (c : ℚ) : realEvaluator y (C c)=(c : ℝ) := by
  simp [realEvaluator]
theorem real_X (y : ℝ) : realEvaluator y X=y := by
  simp [realEvaluator]

theorem eval_parts (p : List ℚ) (y : ℝ) :
    evaluator y (ofList p)=(realEvaluator y (parts p).1 : ℂ)+
      (realEvaluator y (parts p).2 : ℂ)*Complex.I := by
  induction p with
  | nil => simp [ofList,parts]
  | cons c p ih =>
    change evaluator y (C c+X*ofList p)=
      (realEvaluator y (C c-X*(parts p).2) : ℂ)+
        (realEvaluator y (X*(parts p).1) : ℂ)*Complex.I
    simp only [map_add,map_sub,map_mul,complex_C,complex_X,real_C,real_X]
    rw [ih]
    apply Complex.ext <;>
      simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        Complex.ratCast_re,Complex.ratCast_im] <;> ring

def normPolynomial (p : List ℚ) : ℚ[X] := (parts p).1^2+(parts p).2^2

theorem normPolynomial_sound (p : List ℚ) (y : ℝ) :
    realEvaluator y (normPolynomial p)=Complex.normSq (evaluator y (ofList p)) := by
  rw [eval_parts]
  simp [normPolynomial,Complex.normSq_apply,pow_two]

/-- The checker compares complete rational polynomials. Its soundness retains
every real ordinate, including irrational cell endpoints. -/
def normAccepts (p cs : List ℚ) : Bool := decide (ofList cs=normPolynomial p)

theorem normAccepts_sound (p cs : List ℚ) (hc : normAccepts p cs=true) (y : ℝ) :
    realEvaluator y (ofList cs)=Complex.normSq (evaluator y (ofList p)) := by
  rw [show ofList cs=normPolynomial p from of_decide_eq_true hc]
  exact normPolynomial_sound p y

theorem norm_control : normAccepts [2,3] [4,0,9]=true := by
  rw [normAccepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [ofList,normPolynomial,parts]
  all_goals ring
theorem reject_false_norm : normAccepts [2,3] [4,0,8]=false := by
  rw [normAccepts,decide_eq_false_iff_not]
  intro h
  have he := congrArg (fun p : ℚ[X] => p.eval 1) h
  norm_num [ofList,normPolynomial,parts] at he

#print axioms eval_parts
#print axioms normPolynomial_sound
#print axioms normAccepts_sound
#print axioms norm_control
#print axioms reject_false_norm
end
end Gebendorfer.RadenkovicGutman.RationalComplexPolynomial
