/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor251Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor251Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (583371/549755813888)
  b := (700045/549755813888)
  s := [(1099511627765/1099511627776),(-5/1099511627776)]
  L := [(4912547871929/604462909807314587353088),(1965015780375/604462909807314587353088),(294751861777/906694364710971881029632),(1/37778931862957161709568),(-1/56668397794435742564352)]
  c := (614068483991/75557863725914323419136)
  R := (-319197667827969/25000000000000)
  total := (-2689824441/1000000000000000)
  k := 37
  n := 32
  sFloor := (68719476735/137438953472)
  nFloor := (362646438865/18889465931478580854784)
  eFloor := (1785356493621/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=583371,width:=116674,den:=549755813888,localDen:=1813388729421943762059264,lowerC:=14737643615784,s:=[1813388729403801820200960,-8246337208320],L:=[14737643615787,5895047341125,589503723554,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor251Source.source.poly i) 583371 116674 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor251Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 2 WideAnchor251Source.data
    WideAnchor251Source.path_checked WideAnchor251Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor251Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 0 WideAnchor251Source.data
    WideAnchor251Source.path_swapped WideAnchor251Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor251Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor251Cell031
