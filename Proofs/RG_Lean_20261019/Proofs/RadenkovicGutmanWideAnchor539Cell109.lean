/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor539Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor539Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1669171/1048576)
  b := (500751/262144)
  s := [(3394829711349/70368744177664),(-295325788739/17592186044416),(101863198411/35184372088832)]
  L := [(687988882188270995/576460752303423488),(-4193229865/3298534883328),(-4954208835/549755813888),(1009524197/412316860416),(-5393355/17179869184)]
  c := (651637691339/549755813888)
  R := (8500725722647/100000000000000)
  total := (866909520973/31250000000000)
  k := 0
  n := 32
  sFloor := (1208626476607/70368744177664)
  nFloor := 48376681874522112
  eFloor := 36803412325138432
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1669171,width:=333833,den:=1048576,localDen:=1729382256910270464,lowerC:=2049874931500449792,s:=[83431334986113024,-29031706336198656,5006779928297472],L:=[2063966646564812985,-2198460099461120,-15584593450106880,4234251377573888,-542912890798080],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor539Source.source.poly i) 1669171 333833 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor539Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 17) (CoreQuotient.fused G u 5 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 17 WideAnchor539Source.data
    WideAnchor539Source.path_checked WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 5) (CoreQuotient.fused G u 17 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 5 WideAnchor539Source.data
    WideAnchor539Source.path_swapped WideAnchor539Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor539Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor539Cell109
