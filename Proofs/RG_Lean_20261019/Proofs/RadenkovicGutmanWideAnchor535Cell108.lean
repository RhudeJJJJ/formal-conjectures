/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor535Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor535Cell108
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (10867/8192)
  b := (1669171/1048576)
  s := [(4601995833887/70368744177664),(-715034699495/35184372088832),(55725818169/17592186044416)]
  L := [(350210794787242336767/295147905179352825856),(55407190759/3298534883328),(-207044687/17179869184),(993309409/412316860416),(-8411879/34359738368)]
  c := (1304636876237/1099511627776)
  R := (8552931991399/100000000000000)
  total := (11620963227033/500000000000000)
  k := 0
  n := 32
  sFloor := (848707426893/35184372088832)
  nFloor := 1153600223547
  eFloor := 852864538737
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1390976,width:=278195,den:=1048576,localDen:=885443715538058477568,lowerC:=1050632384361283977216,s:=[57906508602166738944,-17994437401384058880,2804772264594112512],L:=[1050632384361727010301,14873254517071151104,-10671001913706676224,2133115713232044032,-216772471217455104],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor535Source.source.poly i) 1390976 278195 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor535Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 13) (CoreQuotient.fused G u 5 13) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 13 WideAnchor535Source.data
    WideAnchor535Source.path_checked WideAnchor535Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor535Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 13 5) (CoreQuotient.fused G u 13 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 13 5 WideAnchor535Source.data
    WideAnchor535Source.path_swapped WideAnchor535Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor535Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor535Cell108
