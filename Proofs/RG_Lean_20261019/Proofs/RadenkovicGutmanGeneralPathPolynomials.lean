/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPolynomialPathMap
import Proofs.RadenkovicGutmanGeneralScaledQuotient

/-! Rational polynomial identities for the four actual coefficients. The shift
is an arbitrary rational, so the mean shift 2-2/N is retained exactly. -/
namespace Gebendorfer.RadenkovicGutman.GeneralPathPolynomials
noncomputable section
open Polynomial PolynomialPathMap GeneralGraphQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sourceSlope (x : ℚ) (p q : ℕ) : ℚ[X] :=
  (denPoly x (p+1)-numPoly x (p+1))*(denPoly x (q+1)-numPoly x (q+1))
def sourceOffset (x : ℚ) (p q : ℕ) : ℚ[X] :=
  2*denPoly x (p+1)*denPoly x (q+1)-numPoly x (p+1)*denPoly x (q+1)-
    numPoly x (q+1)*denPoly x (p+1)
def fusedSlope (x : ℚ) (p q : ℕ) : ℚ[X] := denPoly x (p+q+2)-numPoly x (p+q+2)
def fusedOffset (x : ℚ) (p q : ℕ) : ℚ[X] := denPoly x (p+q+2)
def scalePoly : ℚ[X] := 2*X
def centerPoly (x : ℚ) : ℚ[X] := 2*X*(C x-1)+2*X^2-1
def sourceCenter (x : ℚ) (p q : ℕ) : ℚ[X] :=
  sourceSlope x p q*centerPoly x-scalePoly*sourceOffset x p q
def fusedCenter (x : ℚ) (p q : ℕ) : ℚ[X] :=
  fusedSlope x p q*centerPoly x-scalePoly*fusedOffset x p q

theorem num_evaluation (x : ℚ) (y : ℝ) (n : ℕ) :
    evaluator y (numPoly x n)=PathRecurrence.num (point (x : ℝ) y) n := by
  simpa only [point,Complex.ofReal_ratCast] using eval_num x y n
theorem den_evaluation (x : ℚ) (y : ℝ) (n : ℕ) :
    evaluator y (denPoly x n)=PathRecurrence.den (point (x : ℝ) y) n := by
  simpa only [point,Complex.ofReal_ratCast] using eval_den x y n

theorem sourceSlope_evaluation (x : ℚ) (y : ℝ) (p q : ℕ) :
    evaluator y (sourceSlope x p q)=GeneralScaledQuotient.a x y p q := by
  simp only [sourceSlope,GeneralScaledQuotient.a,numeratorCoefficient,
    map_mul,map_sub,num_evaluation,den_evaluation]
theorem sourceOffset_evaluation (x : ℚ) (y : ℝ) (p q : ℕ) :
    evaluator y (sourceOffset x p q)=sourceConstant (point x y) p q := by
  simp only [sourceOffset,sourceConstant,map_sub,map_mul,map_ofNat,num_evaluation,den_evaluation]
theorem fusedSlope_evaluation (x : ℚ) (y : ℝ) (p q : ℕ) :
    evaluator y (fusedSlope x p q)=GeneralScaledQuotient.c x y p q := by
  simp only [fusedSlope,GeneralScaledQuotient.c,denominatorCoefficient,map_sub,
    num_evaluation,den_evaluation]
theorem fusedOffset_evaluation (x : ℚ) (y : ℝ) (p q : ℕ) :
    evaluator y (fusedOffset x p q)=fusedConstant (point x y) p q := by
  exact den_evaluation x y (p+q+2)
theorem scalePoly_evaluation (y : ℝ) :
    evaluator y scalePoly=GeneralScaledQuotient.scale y := by
  simp [scalePoly,evaluator,GeneralScaledQuotient.scale,mul_assoc]
theorem centerPoly_evaluation (x : ℚ) (y : ℝ) :
    evaluator y (centerPoly x)=GeneralScaledQuotient.centerPolynomial x ((y : ℂ)*Complex.I) := by
  simp [centerPoly,evaluator,GeneralScaledQuotient.centerPolynomial]
theorem sourceCenter_evaluation (x : ℚ) (y : ℝ) (p q : ℕ) :
    evaluator y (sourceCenter x p q)=GeneralScaledQuotient.b x y p q := by
  unfold sourceCenter GeneralScaledQuotient.b
  rw [map_sub,map_mul,sourceSlope_evaluation,centerPoly_evaluation,map_mul,
    scalePoly_evaluation,sourceOffset_evaluation]
theorem fusedCenter_evaluation (x : ℚ) (y : ℝ) (p q : ℕ) :
    evaluator y (fusedCenter x p q)=GeneralScaledQuotient.e x y p q := by
  unfold fusedCenter GeneralScaledQuotient.e
  rw [map_sub,map_mul,fusedSlope_evaluation,centerPoly_evaluation,map_mul,
    scalePoly_evaluation,fusedOffset_evaluation]

def accepts (x : ℚ) (p q : ℕ) (as bs cs es : List ℚ) : Bool :=
  decide (ofList as=sourceSlope x p q ∧ ofList bs=sourceCenter x p q ∧
    ofList cs=fusedSlope x p q ∧ ofList es=fusedCenter x p q)

/-- Closed coefficient checks produce the actual coefficients for every ordinate.
Combined with actual_norm_certificate, they refer to the actual Laplace matrices. -/
theorem accepts_sound (x : ℚ) (p q : ℕ) (as bs cs es : List ℚ)
    (hc : accepts x p q as bs cs es=true) (y : ℝ) :
    evaluator y (ofList as)=GeneralScaledQuotient.a x y p q ∧
      evaluator y (ofList bs)=GeneralScaledQuotient.b x y p q ∧
      evaluator y (ofList cs)=GeneralScaledQuotient.c x y p q ∧
      evaluator y (ofList es)=GeneralScaledQuotient.e x y p q := by
  obtain ⟨ha,hb,hc,he⟩ := of_decide_eq_true hc
  rw [ha,hb,hc,he]
  exact ⟨sourceSlope_evaluation x y p q,sourceCenter_evaluation x y p q,
    fusedSlope_evaluation x y p q,fusedCenter_evaluation x y p q⟩

#print axioms sourceSlope_evaluation
#print axioms sourceOffset_evaluation
#print axioms fusedSlope_evaluation
#print axioms fusedOffset_evaluation
#print axioms scalePoly_evaluation
#print axioms centerPoly_evaluation
#print axioms sourceCenter_evaluation
#print axioms fusedCenter_evaluation
#print axioms accepts_sound
end
end Gebendorfer.RadenkovicGutman.GeneralPathPolynomials
