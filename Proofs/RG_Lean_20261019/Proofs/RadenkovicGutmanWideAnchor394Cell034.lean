/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor394Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor394Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (15751/8589934592)
  b := (302419/137438953472)
  s := [(4398046510907/4398046511104),(-81/4398046511104),(-3/2199023255552)]
  L := [(2461492247289/75557863725914323419136),(1476889488005/113336795588871485128704),(24614727127/18889465931478580854784),(-1/14167099448608935641088)]
  c := (307686530911/9444732965739290427392)
  R := (-120736984180023/10000000000000)
  total := (-4393414141/1000000000000000)
  k := 35
  n := 32
  sFloor := (1099511627705/2199023255552)
  nFloor := (1360974032917/18889465931478580854784)
  eFloor := (467398233235/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=252016,width:=50403,den:=137438953472,localDen:=226673591177742970257408,lowerC:=7384476741864,s:=[226673591167589667569664,-4174708211712,-309237645312],L:=[7384476741867,2953778976010,295376725524,-16],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor394Source.source.poly i) 252016 50403 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor394Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 2 2 WideAnchor394Source.data
    WideAnchor394Source.path_checked WideAnchor394Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor394Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 2 2 WideAnchor394Source.data
    WideAnchor394Source.path_swapped WideAnchor394Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor394Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor394Cell034
