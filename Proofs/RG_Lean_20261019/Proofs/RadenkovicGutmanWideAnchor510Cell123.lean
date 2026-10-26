/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor510Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor510Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (669709/32768)
  b := (1607301/65536)
  s := [(2089749374481/36028797018963968),(-1191388330469/36028797018963968),(39320698153/4503599627370496)]
  L := [(1186057638541792464341/1180591620717411303424),(-2988435397/1649267441664),(36194321/68719476736),(-26117899/206158430208),(83455/4294967296)]
  c := (1103071141459/1099511627776)
  R := (40401623397/25000000000000)
  total := (7897457121713/1000000000000000)
  k := 0
  n := 32
  sFloor := (303231657309/18014398509481984)
  nFloor := 1593454970924350295150438251320897676786722233580871915662175515264946913610651287594321817494345344039253720371003349536866304
  eFloor := 1585927427313379853235604158951142252270984661399447052449330256463415582484284437307980239240940672994295582190825254258999296
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1339418,width:=267883,den:=65536,localDen:=3541774862152233910272,lowerC:=3553240858295846043648,s:=[205430722508980224,-117118238438424576,30923055289860096],L:=[3558172915625377393023,-6417616148161888256,1865441099951112192,-448702088180924416,68819807172034560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor510Source.source.poly i) 1339418 267883 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor510Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 40) (CoreQuotient.fused G u 4 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 40 WideAnchor510Source.data
    WideAnchor510Source.path_checked WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 4) (CoreQuotient.fused G u 40 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 4 WideAnchor510Source.data
    WideAnchor510Source.path_swapped WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor510Cell123
