/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor039Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor039Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1451611/549755813888)
  b := (435483/137438953472)
  s := [(4398046506973/4398046511104),(-1651/4398046511104),(-83/2199023255552)]
  L := [(92933667645280471657430739/332306998946228968225951765070086144),(1584793668197/14167099448608935641088),(39619677907/3541774862152233910272),(7/885443715538058477568),(-1/221360928884514619392)]
  c := (1320666849057/4722366482869645213696)
  R := (-1099871954333727/100000000000000)
  total := (-5758823791/1000000000000000)
  k := 32
  n := 32
  sFloor := (1099511626289/2199023255552)
  nFloor := (1213178076021/4722366482869645213696)
  eFloor := (1018478082685/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1451611,width:=290321,den:=549755813888,localDen:=996920996838686904677855295210258432,lowerC:=278801002935640888436588544,s:=[996920995902298299522599085076905984,-374238099034453643894980608,-37627816135505333062729728],L:=[278801002935841414972292217,111519940211736416834551808,11151947916156517054676992,7881299347898368,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor039Source.source.poly i) 1451611 290321 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor039Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 18) (CoreQuotient.fused G u 10 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 18 WideAnchor039Source.data
    WideAnchor039Source.path_checked WideAnchor039Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor039Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 10) (CoreQuotient.fused G u 18 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 10 WideAnchor039Source.data
    WideAnchor039Source.path_swapped WideAnchor039Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor039Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor039Cell036
