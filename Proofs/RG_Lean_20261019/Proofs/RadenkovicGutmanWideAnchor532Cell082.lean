/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor532Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor532Cell082
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (388831/33554432)
  b := (466597/33554432)
  s := [(1479646903967/4398046511104),(-436450447015/8796093022208),(16673856741/2199023255552)]
  L := [(18960303030867165239/36893488147419103232),(64229090527/1099511627776),(-19402122517/2199023255552),(139994241/137438953472),(-11284067/137438953472)]
  c := (282530531747/549755813888)
  R := (-33284379158217/100000000000000)
  total := (-713549267893/1000000000000000)
  k := 1
  n := 32
  sFloor := (1294769393941/8796093022208)
  nFloor := (186998823631/35184372088832)
  eFloor := (1445343650735/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=388831,width:=77766,den:=33554432,localDen:=36893488147419103232,lowerC:=18960303030857105408,s:=[12412177855792807936,-1830605855716802560,279740896096813056],L:=[18960303030867165239,2155170650510065664,-325513600326172672,37579417920208896,-3029043670679552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor532Source.source.poly i) 388831 77766 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor532Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 10) (CoreQuotient.fused G u 5 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 10 WideAnchor532Source.data
    WideAnchor532Source.path_checked WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 5) (CoreQuotient.fused G u 10 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 5 WideAnchor532Source.data
    WideAnchor532Source.path_swapped WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor532Cell082
