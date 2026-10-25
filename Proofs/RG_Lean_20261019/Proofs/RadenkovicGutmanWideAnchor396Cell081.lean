/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor396Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor396Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (162013/16777216)
  b := (388831/33554432)
  s := [(4392743775775/4398046511104),(-2118330621/4398046511104),(-105152877/2199023255552)]
  L := [(3869139744282828740877091/4951760157141521099596496896),(2110070694643/6755399441055744),(8770282003/281474976710656),(-1621801/105553116266496),(-26779/35184372088832)]
  c := (879740524461/1125899906842624)
  R := (-11447145897/3200000000)
  total := (-1345589640553/200000000000000)
  k := 11
  n := 32
  sFloor := (548801892425/1099511627776)
  nFloor := (245412291447/140737488355328)
  eFloor := (378916505093/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=324026,width:=64805,den:=33554432,localDen:=14855280471424563298789490688,lowerC:=11607419232847512660344832,s:=[14837369423785766725405900800,-7155084746537333541568512,-710349686511203398975488],L:=[11607419232848486222631273,4640094528378719946407936,462865297976308210335744,-228248199352159305728,-11306427602001985536],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor396Source.source.poly i) 324026 64805 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor396Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_checked WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_swapped WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor396Cell081
