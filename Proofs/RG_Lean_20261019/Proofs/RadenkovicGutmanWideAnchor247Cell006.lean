/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor247Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor247Cell006
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (195689/17592186044416)
  b := (939307/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(3255474093383/2475880078570760549798248448),(651093986879/1237940039285380274899124224),(16277328877/309485009821345068724781056)]
  c := (1627737046691/1237940039285380274899124224)
  R := (-171325171995817/10000000000000)
  total := (-18953293/500000000000000)
  k := 50
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (29842047385/9671406556917033397649408)
  eFloor := (442264095223/309485009821345068724781056)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=782756,width:=156551,den:=70368744177664,localDen:=2475880078570760549798248448,lowerC:=3255474093382,s:=[2475880078570197599844827136],L:=[3255474093383,1302187973758,130218631016],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor247Source.source.poly i) 782756 156551 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor247Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 2 WideAnchor247Source.data
    WideAnchor247Source.path_checked WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 2 0 WideAnchor247Source.data
    WideAnchor247Source.path_swapped WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor247Cell006
