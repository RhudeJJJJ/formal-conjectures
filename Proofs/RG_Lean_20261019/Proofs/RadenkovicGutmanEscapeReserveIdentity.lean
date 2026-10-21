/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReserveData
import Proofs.RadenkovicGutmanCorrelatedEscape
import Proofs.RadenkovicGutmanCorrelatedEscapeReduction

/-! Exact original positively cleared polynomial identity; signs are separate. -/
namespace Gebendorfer.RadenkovicGutman.EscapeReserveCertificate
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
abbrev data := EscapeReserveData.data
abbrev degrees := EscapeReserveData.degrees

def form (h x a b : ℝ) : ℝ := h^16*x^16*(1+x^2)^12*CorrelatedEscape.reserve (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)

theorem data_identity (H U a b : ℝ) (hH : H ≠ 0)
    (hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 4 data) ![H,U,a,b] =
      (5663757218217279476064145507376904739888825216556676305544560003094937600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*form (H/46) ((653/2000)+(19347/2000)*U) a b := by
  simp (maxSteps := 10000000) only [data,EscapeReserveData.data,EscapeReservePower00.data,EscapeReservePower01.data,EscapeReservePower02.data,EscapeReservePower03.data,EscapeReservePower04.data,EscapeReservePower05.data,EscapeReservePower06.data,EscapeReservePower07.data,EscapeReservePower08.data,EscapeReservePower09.data,EscapeReservePower10.data,EscapeReservePower11.data,EscapeReservePower12.data,EscapeReservePower13.data,EscapeReservePower14.data,EscapeReservePower15.data,EscapeReservePower16.data,EscapeReservePower17.data,EscapeReservePower18.data,EscapeReservePower19.data,EscapeReservePower20.data,EscapeReservePower21.data,EscapeReservePower22.data,EscapeReservePower23.data,EscapeReservePower24.data,EscapeReservePower25.data,EscapeReservePower26.data,EscapeReservePower27.data,EscapeReservePower28.data,EscapeReservePower29.data,EscapeReservePower30.data,EscapeReservePower31.data,EscapeReservePower32.data,EscapeReservePower33.data,EscapeReservePower34.data,EscapeReservePower35.data,EscapeReservePower36.data,EscapeReservePower37.data,EscapeReservePower38.data,EscapeReservePower39.data,EscapeReservePower40.data,EscapeReservePower41.data,EscapeReservePower42.data,EscapeReservePower43.data,EscapeReservePower44.data,NestedInteger.castPoly,NestedHorner.eval,List.map,List.foldr]
  dsimp only [form]
  rw [CorrelatedEscapeReduction.reserve_reduced]
  have hh : (H/46 : ℝ) ≠ 0 := div_ne_zero hH (by norm_num)
  simp only [CorrelatedEscapeReduction.payment_reciprocal _ _ hh,
    CorrelatedEscapeReduction.radius_reciprocal _ _ hh hX]
  dsimp only [CorrelatedEscapeReduction.factorCore,CorrelatedEscapeReduction.factorLead,
    CorrelatedEscapeReduction.factorBase,CorrelatedEscapeReduction.factorHorizontal,
    CorrelatedEscapeReduction.factorVertical,CorrelatedEscapeReduction.errorWeight]
  field_simp [hH,hX,show (1+((653/2000 : ℝ)+(19347/2000 : ℝ)*U)^2) ≠ 0 by positivity]
  ring

#print axioms data_identity
end
end Gebendorfer.RadenkovicGutman.EscapeReserveCertificate
