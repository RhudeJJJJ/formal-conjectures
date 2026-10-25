/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor021Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor021Cell040
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (376257/68719476736)
  b := (112877/17179869184)
  s := [(2199021924593/2199023255552),(-133095/549755813888),(-26619/1099511627776)]
  L := [(2995785224163/9223372036854775808),(898730213303/6917529027641081856),(14978718821/1152921504606846976),(-5767/864691128455135232),(-3/9007199254740992)]
  c := (1497892612081/4611686018427387904)
  R := (-186750561047401/25000000000000)
  total := (-4038689349/500000000000000)
  k := 22
  n := 32
  sFloor := (2199021338975/4398046511104)
  nFloor := (810579470913/295147905179352825856)
  eFloor := (755230632891/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=376257,width:=75251,den:=68719476736,localDen:=27670116110564327424,lowerC:=8987355672486,s:=[27670099363224354816,-6698890690560,-669889069056],L:=[8987355672489,3594920853212,359489251704,-184544,-9216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor021Source.source.poly i) 376257 75251 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor021Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 30) (CoreQuotient.fused G u 9 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 30 WideAnchor021Source.data
    WideAnchor021Source.path_checked WideAnchor021Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor021Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 9) (CoreQuotient.fused G u 30 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 9 WideAnchor021Source.data
    WideAnchor021Source.path_swapped WideAnchor021Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor021Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor021Cell040
