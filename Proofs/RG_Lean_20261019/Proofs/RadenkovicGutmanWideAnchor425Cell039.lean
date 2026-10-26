/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor425Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor425Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (627095/137438953472)
  b := (376257/68719476736)
  s := [(549755813589/549755813888),(-239/1099511627776),(-3/137438953472)]
  L := [(2161806894109/9444732965739290427392),(1729445514971/18889465931478580854784),(86472275699/9444732965739290427392),(-5/1180591620717411303424),(1/590295810358705651712)]
  c := (2161806894109/9444732965739290427392)
  R := (-22197778667893/2000000000000)
  total := (-125533531/12500000000000)
  k := 33
  n := 32
  sFloor := (1099511626915/2199023255552)
  nFloor := (226503674179/590295810358705651712)
  eFloor := (269045342011/590295810358705651712)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=627095,width:=125419,den:=137438953472,localDen:=18889465931478580854784,lowerC:=4323613788218,s:=[18889465921205019082752,-4105988734976,-412316860416],L:=[4323613788218,1729445514971,172944551398,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor425Source.source.poly i) 627095 125419 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor425Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 6 WideAnchor425Source.data
    WideAnchor425Source.path_checked WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 6 2 WideAnchor425Source.data
    WideAnchor425Source.path_swapped WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor425Cell039
