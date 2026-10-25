/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor246Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor246Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (139979/8388608)
  b := (671899/33554432)
  s := [(4128565839393/4398046511104),(-2878641491/137438953472),(-676007189/1099511627776)]
  L := [(298538780630359350013/9444732965739290427392),(4752311900311/422212465065984),(45237883013/70368744177664),(-1903768273/26388279066624),(8375151/4398046511104)]
  c := (278035905799/8796093022208)
  R := (-86357816605759/50000000000000)
  total := (-5489220912899/1000000000000000)
  k := 5
  n := 32
  sFloor := (1008436320731/2199023255552)
  nFloor := (635841520503/35184372088832)
  eFloor := (1271507424215/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=559916,width:=111983,den:=33554432,localDen:=28334198897217871282176,lowerC:=895616341890331312128,s:=[26598082889363585236992,-593456210916176560128,-17420572611695345664],L:=[895616341891078050039,318922253003552456704,18215177632603963392,-2044155617924349952,53956499466092544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor246Source.source.poly i) 559916 111983 33554432
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
end Gebendorfer.RadenkovicGutman.WideAnchor246Cell084
