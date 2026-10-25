/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor246Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor246Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(1408363958981/72057594037927936),(-1611799816641/144115188075855872),(213443617711/72057594037927936)]
  L := [(2366526127939137306977/2361183241434822606848),(-11799152521/13194139533312),(1734977087/6597069766656),(-52796963/824633720832),(4086841/412316860416)]
  c := (1101246005613/1099511627776)
  R := (39404116331/50000000000000)
  total := (5555022817267/1000000000000000)
  k := 0
  n := 32
  sFloor := (1631815336743/288230376151711744)
  nFloor := 21683810632881168057265754093731303614522508600299328413642827514350610930935174109055923781632
  eFloor := 21634009398843713059827071688664187798208630341389767374115398752342157369467860403162273808384
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=7083549724304467820544,lowerC:=7094723368437701148672,s:=[138447810623668224,-79223184587538432,20982361395462144],L:=[7099578383817411920931,-6334621774776369152,1862917461993586688,-453522458826244096,70211393755807744],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor246Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor246Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 28) (CoreQuotient.fused G u 0 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 28 WideAnchor246Source.data
    WideAnchor246Source.path_checked WideAnchor246Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor246Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 0) (CoreQuotient.fused G u 28 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 0 WideAnchor246Source.data
    WideAnchor246Source.path_swapped WideAnchor246Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor246Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor246Cell125
