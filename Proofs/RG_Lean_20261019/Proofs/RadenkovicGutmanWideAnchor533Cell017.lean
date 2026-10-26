/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor533Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor533Cell017
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (726991/8796093022208)
  b := (872389/8796093022208)
  s := [(2199023253973/2199023255552),(-631/2199023255552),(-1/34359738368)]
  L := [(4298012130977/9444732965739290427392),(5157607458943/28334198897217871282176),(257880017507/14167099448608935641088),(-25/1770887431076116955136),(1/885443715538058477568)]
  c := (134312879093/295147905179352825856)
  R := (-1075528522213057/100000000000000)
  total := (-176233751/1000000000000000)
  k := 32
  n := 32
  sFloor := (1099511626639/2199023255552)
  nFloor := (807350986867/2417851639229258349412352)
  eFloor := (636905688093/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=726991,width:=145398,den:=8796093022208,localDen:=28334198897217871282176,lowerC:=12894036392928,s:=[28334198876872611201024,-8130373091328,-824633720832],L:=[12894036392931,5157607458943,515760035014,-400,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor533Source.source.poly i) 726991 145398 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor533Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 11) (CoreQuotient.fused G u 5 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 11 WideAnchor533Source.data
    WideAnchor533Source.path_checked WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 5) (CoreQuotient.fused G u 11 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 5 WideAnchor533Source.data
    WideAnchor533Source.path_swapped WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor533Cell017
