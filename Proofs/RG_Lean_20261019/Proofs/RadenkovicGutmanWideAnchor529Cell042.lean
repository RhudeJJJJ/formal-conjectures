/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor529Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor529Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1083619/137438953472)
  b := (650171/68719476736)
  s := [(1099511624967/1099511627776),(-1123/1099511627776),(-113/1099511627776)]
  L := [(1944334857455/2361183241434822606848),(4666386432257/14167099448608935641088),(233318460287/7083549724304467820544),(-5/885443715538058477568),(1/442721857769029238784)]
  c := (1944334857455/2361183241434822606848)
  R := (-209175087608457/20000000000000)
  total := (-16344265283/1000000000000000)
  k := 31
  n := 32
  sFloor := (1099511623731/2199023255552)
  nFloor := (703126920187/590295810358705651712)
  eFloor := (1090667588841/590295810358705651712)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1083619,width:=216723,den:=137438953472,localDen:=14167099448608935641088,lowerC:=11666009144730,s:=[14167099412415246237696,-14469744820224,-1455993913344],L:=[11666009144730,4666386432257,466636920574,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor529Source.source.poly i) 1083619 216723 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor529Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 8 WideAnchor529Source.data
    WideAnchor529Source.path_checked WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 8 4 WideAnchor529Source.data
    WideAnchor529Source.path_swapped WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor529Cell042
