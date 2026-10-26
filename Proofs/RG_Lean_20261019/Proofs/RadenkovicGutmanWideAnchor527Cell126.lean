/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor527Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor527Cell126
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (144657/4096)
  b := (1388707/32768)
  s := [(1630511207801/144115188075855872),(-1866350074561/288230376151711744),(247187375065/144115188075855872)]
  L := [(73903275464705070659/73786976294838206464),(-8232063463/13194139533312),(404165211/2199023255552),(-36953891/824633720832),(954489/137438953472)]
  c := (1100719061827/1099511627776)
  R := (1714925533/3125000000000)
  total := (4643304344631/1000000000000000)
  k := 0
  n := 32
  sFloor := (1889047091171/576460752303423488)
  nFloor := 56341390245886635264742700289838919240086716416
  eFloor := 56251454419744677931094418309389582899999670272
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1157256,width:=231451,den:=32768,localDen:=221360928884514619392,lowerC:=221604017467067203584,s:=[2504465215182336,-1433356857262848,379679808099840],L:=[221709826394115211977,-138111106844459008,40684602267795456,-9919734581559296,1537312139771904],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor527Source.source.poly i) 1157256 231451 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor527Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 7) (CoreQuotient.fused G u 4 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 7 WideAnchor527Source.data
    WideAnchor527Source.path_checked WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 4) (CoreQuotient.fused G u 7 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 4 WideAnchor527Source.data
    WideAnchor527Source.path_swapped WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor527Cell126
