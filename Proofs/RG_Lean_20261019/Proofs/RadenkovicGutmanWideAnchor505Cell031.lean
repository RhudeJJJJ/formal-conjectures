/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor505Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor505Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(2199023252491/2199023255552),(-1225/2199023255552),(-61/1099511627776)]
  L := [(245276725926249209971673033/332306998946228968225951765070086144),(2788468746653/9444732965739290427392),(418269590683/14167099448608935641088),(-31/590295810358705651712),(-7/885443715538058477568)]
  c := (1742795958579/2361183241434822606848)
  R := (-1051346900374663/100000000000000)
  total := (-2211367899/1000000000000000)
  k := 31
  n := 32
  sFloor := (274877906393/549755813888)
  nFloor := (962741104005/9444732965739290427392)
  eFloor := (453879008229/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=996920996838686904677855295210258432,lowerC:=735830177778674135765876736,s:=[996920995450991179487712831294406656,-555350298385470277130649600,-55308356247369284742807552],L:=[735830177778747629915019099,294331565820954487856037888,29433105824068260711104512,-52354345668182016,-7881299347898368],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor505Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor505Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 35) (CoreQuotient.fused G u 4 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 35 WideAnchor505Source.data
    WideAnchor505Source.path_checked WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 4) (CoreQuotient.fused G u 35 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 4 WideAnchor505Source.data
    WideAnchor505Source.path_swapped WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor505Cell031
