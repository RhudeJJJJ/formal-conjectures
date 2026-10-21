/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalComplexPolynomial
import Mathlib.Analysis.Complex.Norm

namespace Gebendorfer.RadenkovicGutman.RationalMobiusPolynomials
open Polynomial PolynomialPathMap RationalComplexPolynomial
set_option maxHeartbeats 0

def U (a b c e : List ℚ) : ℚ[X] :=
  let ar := (parts a).1; let ai := (parts a).2
  let br := (parts b).1; let bi := (parts b).2
  let cr := (parts c).1; let ci := (parts c).2
  let er := (parts e).1; let ei := (parts e).2
  (br*er+bi*ei-ar*cr-ai*ci)^2+(bi*er-br*ei-ai*cr+ar*ci)^2
def V (a b c e : List ℚ) : ℚ[X] :=
  let ar := (parts a).1; let ai := (parts a).2
  let br := (parts b).1; let bi := (parts b).2
  let cr := (parts c).1; let ci := (parts c).2
  let er := (parts e).1; let ei := (parts e).2
  (ar*er-ai*ei-br*cr+bi*ci)^2+(ar*ei+ai*er-br*ci-bi*cr)^2
def N (a b : List ℚ) : ℚ[X] := normPolynomial b-normPolynomial a
def E (c e : List ℚ) : ℚ[X] := normPolynomial e-normPolynomial c
def J (a b : List ℚ) : ℚ[X] := (N a b)^2

theorem U_sound (a b c e : List ℚ) (y : ℝ) :
    realEvaluator y (U a b c e)=
      ‖evaluator y (ofList b)*star (evaluator y (ofList e))-
        evaluator y (ofList a)*star (evaluator y (ofList c))‖^2 := by
  rw [eval_parts b y,eval_parts e y,eval_parts a y,eval_parts c y]
  simp [U,Complex.sq_norm,Complex.normSq_apply]
  all_goals ring
theorem V_sound (a b c e : List ℚ) (y : ℝ) :
    realEvaluator y (V a b c e)=
      ‖evaluator y (ofList a)*evaluator y (ofList e)-
        evaluator y (ofList b)*evaluator y (ofList c)‖^2 := by
  rw [eval_parts a y,eval_parts e y,eval_parts b y,eval_parts c y]
  simp [V,Complex.sq_norm,Complex.normSq_apply]
  all_goals ring
theorem N_sound (a b : List ℚ) (y : ℝ) :
    realEvaluator y (N a b)=
      Complex.normSq (evaluator y (ofList b))-Complex.normSq (evaluator y (ofList a)) := by
  rw [N,map_sub,normPolynomial_sound,normPolynomial_sound]
theorem E_sound (c e : List ℚ) (y : ℝ) :
    realEvaluator y (E c e)=
      Complex.normSq (evaluator y (ofList e))-Complex.normSq (evaluator y (ofList c)) := by
  exact N_sound c e y
theorem J_sound (a b : List ℚ) (y : ℝ) :
    realEvaluator y (J a b)=
      (Complex.normSq (evaluator y (ofList b))-Complex.normSq (evaluator y (ofList a)))^2 := by
  rw [J,map_pow,N_sound]

def accepts (a b c e us vs js ns es : List ℚ) : Bool :=
  decide (ofList us=U a b c e ∧ ofList vs=V a b c e ∧ ofList js=J a b ∧
    ofList ns=N a b ∧ ofList es=E c e)

theorem accepts_sound (a b c e us vs js ns es : List ℚ)
    (hc : accepts a b c e us vs js ns es=true) (y : ℝ) :
    realEvaluator y (ofList us)=
      ‖evaluator y (ofList b)*star (evaluator y (ofList e))-
        evaluator y (ofList a)*star (evaluator y (ofList c))‖^2 ∧
    realEvaluator y (ofList vs)=
      ‖evaluator y (ofList a)*evaluator y (ofList e)-
        evaluator y (ofList b)*evaluator y (ofList c)‖^2 ∧
    realEvaluator y (ofList js)=
      (Complex.normSq (evaluator y (ofList b))-Complex.normSq (evaluator y (ofList a)))^2 ∧
    realEvaluator y (ofList ns)=
      Complex.normSq (evaluator y (ofList b))-Complex.normSq (evaluator y (ofList a)) ∧
    realEvaluator y (ofList es)=
      Complex.normSq (evaluator y (ofList e))-Complex.normSq (evaluator y (ofList c)) := by
  obtain ⟨hu,hv,hj,hn,he⟩ := of_decide_eq_true hc
  rw [hu,hv,hj,hn,he]
  exact ⟨U_sound a b c e y,V_sound a b c e y,J_sound a b y,N_sound a b y,E_sound c e y⟩

#print axioms U_sound
#print axioms V_sound
#print axioms N_sound
#print axioms E_sound
#print axioms J_sound
#print axioms accepts_sound
end Gebendorfer.RadenkovicGutman.RationalMobiusPolynomials
