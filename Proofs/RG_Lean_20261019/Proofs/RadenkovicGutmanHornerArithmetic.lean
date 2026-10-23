/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanHornerCertificates
import Proofs.RadenkovicGutmanRationalComplexPolynomial

namespace Gebendorfer.RadenkovicGutman.HornerArithmetic
open HornerCertificates

def mul : Poly → Poly → Poly
  | [], _ => []
  | c :: p, q => add (scale c q) (0 :: mul p q)

def floorMargin (p : Poly) (c : ℚ) : Poly := add p [-c]

def normMargin (s L U V J : Poly) : Poly :=
  add (mul s J) (scale (-1) (mul L
    (add (mul (add s (mul s s)) U) (mul (add s [1]) V))))

noncomputable section

theorem evaluate_mul (p q : Poly) (x : ℝ) :
    evaluate (mul p q) x = evaluate p x * evaluate q x := by
  induction p with
  | nil => simp [mul]
  | cons c p ih =>
      simp only [mul,evaluate_add,evaluate_scale,evaluate_cons,ih,Rat.cast_zero]
      ring

theorem evaluate_floorMargin (p : Poly) (c : ℚ) (x : ℝ) :
    evaluate (floorMargin p c) x = evaluate p x-(c : ℝ) := by
  simp [floorMargin,evaluate_add,sub_eq_add_neg]

theorem evaluate_normMargin (s L U V J : Poly) (x : ℝ) :
    evaluate (normMargin s L U V J) x = evaluate s x*evaluate J x-
      evaluate L x*((evaluate s x+(evaluate s x)^2)*evaluate U x+
        (evaluate s x+1)*evaluate V x) := by
  simp only [normMargin,evaluate_add,evaluate_scale,evaluate_mul,evaluate_cons,
    evaluate_nil,Rat.cast_neg,Rat.cast_one,mul_zero,add_zero]
  ring

theorem real_evaluation (p : Poly) (x : ℝ) :
    evaluate p x = RationalComplexPolynomial.realEvaluator x (PolynomialPathMap.ofList p) := by
  induction p with
  | nil => simp [PolynomialPathMap.ofList]
  | cons c p ih =>
      simp only [evaluate_cons,PolynomialPathMap.ofList,map_add,map_mul,
        RationalComplexPolynomial.real_C,RationalComplexPolynomial.real_X,ih]

#print axioms evaluate_mul
#print axioms evaluate_floorMargin
#print axioms evaluate_normMargin
#print axioms real_evaluation
end
end Gebendorfer.RadenkovicGutman.HornerArithmetic
