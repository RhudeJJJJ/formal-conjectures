/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor535Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor535Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1451611/549755813888)
  b := (435483/137438953472)
  s := [(4398043499655/4398046511104),(-1204571/4398046511104),(-60229/2199023255552)]
  L := [(4558604605304407300057888815/10384593717069655257060992658440192),(4858601626169/27670116110564327424),(242928402617/13835058055282163712),(-16853/1729382256910270464),(-425/864691128455135232)]
  c := (506106779297/1152921504606846976)
  R := (-146388173233471/20000000000000)
  total := (-3815813519/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199021087313/4398046511104)
  nFloor := (895718885747/2361183241434822606848)
  eFloor := (1397156523871/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1451611,width:=290321,den:=549755813888,localDen:=31153781151208965771182977975320576,lowerC:=13675813815909906357128527872,s:=[31153759819460232064217664265912320,-8532638574955157107060506624,-853270232690267584727089152],L:=[13675813815913221900173666445,5470299118289098576763027456,547026131751815512657494016,-303596658080299876352,-15312238733059686400],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor535Source.source.poly i) 1451611 290321 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor535Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 13) (CoreQuotient.fused G u 5 13) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 13 WideAnchor535Source.data
    WideAnchor535Source.path_checked WideAnchor535Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor535Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 13 5) (CoreQuotient.fused G u 13 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 13 5 WideAnchor535Source.data
    WideAnchor535Source.path_swapped WideAnchor535Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor535Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor535Cell036
