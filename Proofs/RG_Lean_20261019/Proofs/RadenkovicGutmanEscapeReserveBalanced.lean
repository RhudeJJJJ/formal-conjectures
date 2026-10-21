/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeFactorSigns
namespace Gebendorfer.RadenkovicGutman.EscapeReserveBalanced
open CorrelatedEscapeReduction
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def p (x : ℝ) : ℝ := 1+x^2
def A (h x a : ℝ) : ℝ := x^2+a*h^2
def Z (h x a b : ℝ) : ℝ := A h x a*A h x b+h^2*x^2
def E (h x : ℝ) : ℝ :=
  -(42/25 : ℝ)*(p x)^2+((42/25 : ℝ)^2/2)*h*p x-((42/25 : ℝ)^3/6)*h^2
def L (h x a b : ℝ) : ℝ :=
  E h x*(h^2*x^2+(A h x a)^2)*(h^2*x^2+(A h x b)^2)-
    h*x^2*(p x)^3*(x^2+2*a*h^2)*(x^2+2*b*h^2)
def B (h x a b : ℝ) : ℝ := E h x*(4*h^2+x^2)*(Z h x a b)^2
def X (h x a b : ℝ) : ℝ :=
  2*Z h x a b*(h*E h x*(2*A h x a*A h x b-2*h^2*x^2-x^2*(A h x a+A h x b))-
    (p x)^3*x^2*(4*h^2+x^2))
def V (h x a b : ℝ) : ℝ :=
  2*E h x*Z h x a b*(A h x a*A h x b-h^2*x^2+2*h^2*(A h x a+A h x b))
def U (h x a b : ℝ) : ℝ := B h x a b+L h x a b-X h x a b
def balanced (h x a b : ℝ) : ℝ :=
  x^2*(U h x a b)^2+h*x^2*U h x a b*V h x a b+
    (h^2/4)*(4*L h x a b*B h x a b-(X h x a b)^2)

theorem p_ne_zero (x : ℝ) : p x ≠ 0 := by unfold p; positivity

theorem arm_fraction (h x a : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    x/h+a*h/x=A h x a/(h*x) := by
  unfold A
  field_simp [hh,hx]

theorem error_fraction (h x : ℝ) (hh : h ≠ 0) :
    errorWeight (CorrelatedEscape.payment (1/h) x)=h*E h x/(p x)^3 := by
  rw [payment_reciprocal h x hh]
  unfold errorWeight E p
  field_simp [show (1+x^2) ≠ 0 by positivity]
  ring

theorem lead_fraction (h x a b : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    factorLead (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)=
      L h x a b/(h^3*x^4*(p x)^3) := by
  unfold factorLead
  rw [error_fraction h x hh,arm_fraction h x a hh hx,arm_fraction h x b hh hx]
  dsimp only [L,A]
  field_simp [hh,hx,p_ne_zero x]
  ring

theorem base_fraction (h x a b : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    factorBase (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)=
      B h x a b/(h^5*x^4*(p x)^3) := by
  unfold factorBase
  rw [error_fraction h x hh,arm_fraction h x a hh hx,arm_fraction h x b hh hx]
  dsimp only [B,Z,A]
  field_simp [hh,hx,p_ne_zero x]

theorem horizontal_fraction (h x a b : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    factorHorizontal (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)=
      X h x a b/(h^4*x^4*(p x)^3) := by
  unfold factorHorizontal
  rw [error_fraction h x hh,arm_fraction h x a hh hx,arm_fraction h x b hh hx]
  dsimp only [X,Z,A]
  field_simp [hh,hx,p_ne_zero x]
  ring

theorem vertical_fraction (h x a b : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    factorVertical (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)=
      V h x a b/(h^4*x^3*(p x)^3) := by
  unfold factorVertical
  rw [error_fraction h x hh,arm_fraction h x a hh hx,arm_fraction h x b hh hx]
  dsimp only [V,Z,A]
  field_simp [hh,hx,p_ne_zero x]

theorem core_fraction (h x a b : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    factorCore (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)=
      U h x a b/(h^5*x^4*(p x)^3) := by
  unfold factorCore
  rw [base_fraction h x a b hh hx,lead_fraction h x a b hh hx,horizontal_fraction h x a b hh hx]
  dsimp only [U]
  field_simp [hh,hx,p_ne_zero x]

theorem inner_clearing (h x a b : ℝ) (hh : h ≠ 0) (hx : x ≠ 0) :
    h^10*x^10*(1+x^2)^6*EscapeFactorSigns.reserveInner (1/h) (x/h)
      (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)=balanced h x a b := by
  dsimp only [EscapeFactorSigns.reserveInner]
  simp only [core_fraction h x a b hh hx,lead_fraction h x a b hh hx,
    base_fraction h x a b hh hx,horizontal_fraction h x a b hh hx,
    vertical_fraction h x a b hh hx,radius_reciprocal h x hh hx]
  change h^10*x^10*(p x)^6*_=balanced h x a b
  dsimp only [balanced]
  field_simp [hh,hx,p_ne_zero x]
  ring

#print axioms arm_fraction
#print axioms error_fraction
#print axioms lead_fraction
#print axioms base_fraction
#print axioms horizontal_fraction
#print axioms vertical_fraction
#print axioms core_fraction
#print axioms inner_clearing
end
end Gebendorfer.RadenkovicGutman.EscapeReserveBalanced
