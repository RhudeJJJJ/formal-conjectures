/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor507Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor507Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (669709/32768)
  b := (1607301/65536)
  s := [(2089749374481/36028797018963968),(-1191388330469/36028797018963968),(39320698153/4503599627370496)]
  L := [(1186057638498249273249/1180591620717411303424),(-2988435397/1649267441664),(36194321/68719476736),(-26117899/206158430208),(83455/4294967296)]
  c := (551535570709/549755813888)
  R := (16160649173/10000000000000)
  total := (3948728523321/500000000000000)
  k := 0
  n := 32
  sFloor := (303231657309/18014398509481984)
  nFloor := 21552719282288358741737229168615961919092221165778609490493177952690874002984416650543469424763262561246734463640010752
  eFloor := 21450903393387256488220630954605129864463071229344343043107997219267041612626919662403603506909751925441168982222569472
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1339418,width:=267883,den:=65536,localDen:=3541774862152233910272,lowerC:=3553240858163775799296,s:=[205430722508980224,-117118238438424576,30923055289860096],L:=[3558172915494747819747,-6417616148161888256,1865441099951112192,-448702088180924416,68819807172034560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor507Source.source.poly i) 1339418 267883 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor507Source.source witness geometry=true := by
  unfold IntegerPolynomialPaymentCell.checks
  rw [decide_eq_true_eq]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by intro i; rfl,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem budget : SemanticPolynomialPaymentCell.Budget witness := by
  unfold SemanticPolynomialPaymentCell.Budget
  decide +kernel
theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 37) (CoreQuotient.fused G u 4 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 37 WideAnchor507Source.data
    WideAnchor507Source.path_checked WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 4) (CoreQuotient.fused G u 37 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 4 WideAnchor507Source.data
    WideAnchor507Source.path_swapped WideAnchor507Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor507Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor507Cell123
