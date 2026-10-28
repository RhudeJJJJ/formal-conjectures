/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor513Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor513Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1123495/68719476736)
  b := (674097/34359738368)
  s := [(4398045387269/4398046511104),(-449533/4398046511104),(-22477/2199023255552)]
  L := [(1223444751025/9223372036854775808),(978755301287/18446744073709551616),(146812995481/27670116110564327424),(-1249/576460752303423488),(-187/1729382256910270464)]
  c := (1223444751025/9223372036854775808)
  R := (-395889520324119/50000000000000)
  total := (-25583111109/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022446391/4398046511104)
  nFloor := (2067719323379/73786976294838206464)
  eFloor := (995817306657/36893488147419103232)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1123495,width:=224699,den:=68719476736,localDen:=55340232221128654848,lowerC:=7340668506150,s:=[55340218080011747328,-5656434180096,-565652226048],L:=[7340668506150,2936265903861,293625990962,-119904,-5984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor513Source.source.poly i) 1123495 224699 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor513Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 43) (CoreQuotient.fused G u 4 43) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 43 WideAnchor513Source.data
    WideAnchor513Source.path_checked WideAnchor513Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor513Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 43 4) (CoreQuotient.fused G u 43 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 43 4 WideAnchor513Source.data
    WideAnchor513Source.path_swapped WideAnchor513Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor513Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor513Cell046
