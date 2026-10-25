/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor279Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor279Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1083619/137438953472)
  b := (650171/68719476736)
  s := [(2199023252633/2199023255552),(-2335/4398046511104),(-117/2199023255552)]
  L := [(487241816107/590295810358705651712),(2338752081835/7083549724304467820544),(116937171989/3541774862152233910272),(-1/27670116110564327424),(1/221360928884514619392)]
  c := (487241816107/590295810358705651712)
  R := (-104575645397647/10000000000000)
  total := (-8171194531/500000000000000)
  k := 31
  n := 32
  sFloor := (549755812837/1099511627776)
  nFloor := (1671450786921/1180591620717411303424)
  eFloor := (1343911114643/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1083619,width:=216723,den:=137438953472,localDen:=7083549724304467820544,lowerC:=5846901793284,s:=[7083549714901710667776,-3760780738560,-376883380224],L:=[5846901793284,2338752081835,233874343978,-256,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor279Source.source.poly i) 1083619 216723 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor279Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 0 6 WideAnchor279Source.data
    WideAnchor279Source.path_checked WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 6 0 WideAnchor279Source.data
    WideAnchor279Source.path_swapped WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor279Cell042
