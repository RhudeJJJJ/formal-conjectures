/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor522Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor522Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (869545/8589934592)
  b := (521727/4294967296)
  s := [(4398045121383/4398046511104),(-555891/4398046511104),(-27793/2199023255552)]
  L := [(581353234071/4611686018427387904),(1395247699781/27670116110564327424),(46508248397/9223372036854775808),(-311/1729382256910270464),(-5/576460752303423488)]
  c := (581353234071/4611686018427387904)
  R := (-794325040481751/100000000000000)
  total := (-158918767369/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022254953/4398046511104)
  nFloor := (490106742397/2305843009213693952)
  eFloor := (1228508420403/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=869545,width:=173909,den:=8589934592,localDen:=27670116110564327424,lowerC:=3488119404426,s:=[27670107367195803648,-3497363767296,-349716873216],L:=[3488119404426,1395247699781,139524745191,-4976,-240],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor522Source.source.poly i) 869545 173909 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor522Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 4 6 WideAnchor522Source.data
    WideAnchor522Source.path_checked WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 6 4 WideAnchor522Source.data
    WideAnchor522Source.path_swapped WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor522Cell056
