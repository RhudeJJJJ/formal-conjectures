/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor275Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor275Cell107
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1159147/1048576)
  b := (10867/8192)
  s := [(1903218256781/17592186044416),(-598171845545/17592186044416),(96410776821/17592186044416)]
  L := [(176420641976744356861/147573952589676412928),(256495385725/6597069766656),(-60176285159/3298534883328),(712686559/206158430208),(-75463987/206158430208)]
  c := (164304526501/137438953472)
  R := (8927086555563/100000000000000)
  total := (2103582634921/100000000000000)
  k := 0
  n := 32
  sFloor := (1401457188057/35184372088832)
  nFloor := (866707079429/134217728)
  eFloor := (18232438061/4194304)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1159147,width:=231829,den:=1048576,localDen:=442721857769029238784,lowerC:=529261925929920233472,s:=[47896055683737452544,-15053487386740654080,2426256641180565504],L:=[529261925930233070583,17213113957246566400,-8076724273521098752,1530482731601887232,-162057678095384576],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor275Source.source.poly i) 1159147 231829 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor275Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 0 4 WideAnchor275Source.data
    WideAnchor275Source.path_checked WideAnchor275Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor275Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 0 WideAnchor275Source.data
    WideAnchor275Source.path_swapped WideAnchor275Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor275Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor275Cell107
