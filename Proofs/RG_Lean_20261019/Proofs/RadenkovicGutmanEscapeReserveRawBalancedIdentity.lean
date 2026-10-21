/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReserveRawData
import Proofs.RadenkovicGutmanEscapeReserveBalanced
namespace Gebendorfer.RadenkovicGutman.EscapeReserveRawBalancedIdentity
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem data_identity (h x a b : ℝ) :
    NestedHorner.eval (NestedInteger.castPoly 4 EscapeReserveRawData.data) ![h,x,a,b]*x^2 =
      (1258948562770990142036812121880765399040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*
        EscapeReserveBalanced.balanced h x a b := by
  rw [EscapeReserveRawData.data_eval]
  dsimp only [EscapeReserveBalanced.balanced,EscapeReserveBalanced.U,
    EscapeReserveBalanced.L,EscapeReserveBalanced.B,EscapeReserveBalanced.X,
    EscapeReserveBalanced.V,EscapeReserveBalanced.Z,EscapeReserveBalanced.A,
    EscapeReserveBalanced.E,EscapeReserveBalanced.p]
  norm_num only [Rat.cast_intCast]
  ring
#print axioms data_identity
end
end Gebendorfer.RadenkovicGutman.EscapeReserveRawBalancedIdentity
