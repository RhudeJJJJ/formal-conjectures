/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor014Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor014Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302419/137438953472)
  b := (1451611/549755813888)
  s := [(2199022677449/2199023255552),(-462479/4398046511104),(-23125/2199023255552)]
  L := [(890171904099/4611686018427387904),(2136410225971/27670116110564327424),(17803384575/2305843009213693952),(-1445/864691128455135232),(-3/36028797018963968)]
  c := (890171904099/4611686018427387904)
  R := (-773022238151109/100000000000000)
  total := (-1680322579/500000000000000)
  k := 23
  n := 32
  sFloor := (549755605771/1099511627776)
  nFloor := (1169734983457/2361183241434822606848)
  eFloor := (796559955869/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1209676,width:=241935,den:=549755813888,localDen:=27670116110564327424,lowerC:=5341031424594,s:=[27670108836345151488,-2909666279424,-290979840000],L:=[5341031424594,2136410225971,213640614900,-46240,-2304],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor014Source.source.poly i) 1209676 241935 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor014Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 23) (CoreQuotient.fused G u 9 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 23 WideAnchor014Source.data
    WideAnchor014Source.path_checked WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 9) (CoreQuotient.fused G u 23 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 9 WideAnchor014Source.data
    WideAnchor014Source.path_swapped WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor014Cell035
