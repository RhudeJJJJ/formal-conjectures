/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor428Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor428Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (724621/8589934592)
  b := (869545/8589934592)
  s := [(4398045576373/4398046511104),(-373891/4398046511104),(-18695/2199023255552)]
  L := [(4499485808631/73786976294838206464),(5399375391611/221360928884514619392),(89989457185/36893488147419103232),(-641/13835058055282163712),(-5/2305843009213693952)]
  c := (1124871452157/18446744073709551616)
  R := (-830636483776481/100000000000000)
  total := (-138558395277/1000000000000000)
  k := 24
  n := 32
  sFloor := (1099511291273/2199023255552)
  nFloor := (404392478119/4611686018427387904)
  eFloor := (704720141669/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=724621,width:=144924,den:=8589934592,localDen:=221360928884514619392,lowerC:=13498457425884,s:=[221360881837962952704,-18818550202368,-1881900318720],L:=[13498457425893,5399375391611,539936743110,-10256,-480],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor428Source.source.poly i) 724621 144924 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor428Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 6 WideAnchor428Source.data
    WideAnchor428Source.path_checked WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 2 WideAnchor428Source.data
    WideAnchor428Source.path_swapped WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor428Cell055
