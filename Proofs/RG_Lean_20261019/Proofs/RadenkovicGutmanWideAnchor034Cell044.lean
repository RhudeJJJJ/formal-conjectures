/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor034Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor034Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (780205/68719476736)
  b := (468123/34359738368)
  s := [(549755344507/549755813888),(-751009/2199023255552),(-18775/549755813888)]
  L := [(4148670971885/9223372036854775808),(2489200071505/13835058055282163712),(10371625107/576460752303423488),(-12565/864691128455135232),(-13/18014398509481984)]
  c := (1037167742971/2305843009213693952)
  R := (-730723161206723/100000000000000)
  total := (-3275931923/200000000000000)
  k := 22
  n := 32
  sFloor := (2199020551919/4398046511104)
  nFloor := (539421911579/73786976294838206464)
  eFloor := (255979479025/36893488147419103232)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=780205,width:=156041,den:=68719476736,localDen:=27670116110564327424,lowerC:=12446012915652,s:=[27670092485845057536,-9449880158208,-944976691200],L:=[12446012915655,4978400143010,497838005136,-402080,-19968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor034Source.source.poly i) 780205 156041 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor034Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 13) (CoreQuotient.fused G u 10 13) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 13 WideAnchor034Source.data
    WideAnchor034Source.path_checked WideAnchor034Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor034Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 13 10) (CoreQuotient.fused G u 13 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 13 10 WideAnchor034Source.data
    WideAnchor034Source.path_swapped WideAnchor034Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor034Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor034Cell044
