/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor431Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor431Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (15751/8589934592)
  b := (302419/137438953472)
  s := [(549755813823/549755813888),(-207/4398046511104),(-11/2199023255552)]
  L := [(15389926893/295147905179352825856),(1181941695337/56668397794435742564352),(59096850269/28334198897217871282176),(-1/885443715538058477568),(1/1770887431076116955136)]
  c := (15389926893/295147905179352825856)
  R := (-1183851462179139/100000000000000)
  total := (-2153582583/500000000000000)
  k := 35
  n := 32
  sFloor := (2199023255177/4398046511104)
  nFloor := (1457314263561/18889465931478580854784)
  eFloor := (1651087442431/18889465931478580854784)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=252016,width:=50403,den:=137438953472,localDen:=56668397794435742564352,lowerC:=2954865963456,s:=[56668397787735593582592,-2667174690816,-283467841536],L:=[2954865963456,1181941695337,118193700538,-64,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor431Source.source.poly i) 252016 50403 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor431Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 2 8 WideAnchor431Source.data
    WideAnchor431Source.path_checked WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 8 2 WideAnchor431Source.data
    WideAnchor431Source.path_swapped WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor431Cell034
