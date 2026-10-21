/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReducedReserve
import Proofs.RadenkovicGutmanEscapeFactorSigns
namespace Gebendorfer.RadenkovicGutman.EscapeReducedReserveIdentity
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
def form (h x a b : ℝ) : ℝ := h^10*x^8*(1+x^2)^6*
  EscapeFactorSigns.reserveInner (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)
theorem data_identity (H U a b : ℝ) (hH : H ≠ 0)
    (hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 4 EscapeReducedReserve.data) ![H,U,a,b] =
      (1258948562770990142036812121880765399040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*form (H/46) ((653/2000)+(19347/2000)*U) a b := by
  dsimp only [form,EscapeFactorSigns.reserveInner]
  have hh : (H/46 : ℝ) ≠ 0 := div_ne_zero hH (by norm_num)
  simp only [CorrelatedEscapeReduction.payment_reciprocal _ _ hh,
    CorrelatedEscapeReduction.radius_reciprocal _ _ hh hX]
  dsimp only [CorrelatedEscapeReduction.factorCore,CorrelatedEscapeReduction.factorLead,
    CorrelatedEscapeReduction.factorBase,CorrelatedEscapeReduction.factorHorizontal,
    CorrelatedEscapeReduction.factorVertical,CorrelatedEscapeReduction.errorWeight]
  have hlin : (653 : ℝ)+19347*U ≠ 0 := by
    intro hz
    apply hX
    nlinarith only [hz]
  have hquad : (426409 : ℝ)+25267182*U+374306409*U^2 ≠ 0 := by
    rw [show (426409 : ℝ)+25267182*U+374306409*U^2=((653 : ℝ)+19347*U)^2 by ring]
    exact pow_ne_zero 2 hlin
  have hpn : (4426409 : ℝ)+25267182*U+374306409*U^2 ≠ 0 := by
    rw [show (4426409 : ℝ)+25267182*U+374306409*U^2=4000000+((653 : ℝ)+19347*U)^2 by ring]
    positivity
  field_simp [hH,hX,hlin,hquad,hpn,show (1+((653/2000 : ℝ)+(19347/2000 : ℝ)*U)^2) ≠ 0 by positivity]
  rw [EscapeReducedReserve.data_eval]
  norm_num only [Rat.cast_intCast]
  ring
#print axioms data_identity
end
end Gebendorfer.RadenkovicGutman.EscapeReducedReserveIdentity
