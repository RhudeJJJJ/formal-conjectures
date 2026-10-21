/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReducedReserve
import Proofs.RadenkovicGutmanEscapeFactorSigns
import Proofs.RadenkovicGutmanEscapeReserveRawAffine
import Proofs.RadenkovicGutmanEscapeReserveRawBalancedIdentity
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

  have hh : (H/46 : ℝ) ≠ 0 := div_ne_zero hH (by norm_num)
  have h := EscapeReserveRawBalancedIdentity.data_identity (H/46)
    ((653/2000)+(19347/2000)*U) a b
  rw [← EscapeReserveRawAffine.evaluation H U a b] at h
  rw [← EscapeReserveBalanced.inner_clearing (H/46)
    ((653/2000)+(19347/2000)*U) a b hh hX] at h
  apply mul_right_cancel₀ (pow_ne_zero 2 hX)
  convert h using 1
  dsimp only [form]
  ring

#print axioms data_identity
end
end Gebendorfer.RadenkovicGutman.EscapeReducedReserveIdentity
