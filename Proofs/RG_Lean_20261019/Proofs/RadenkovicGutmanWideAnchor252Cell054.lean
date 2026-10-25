/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor252Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor252Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (603851/8589934592)
  b := (724621/8589934592)
  s := [(2199005547129/2199023255552),(-7083237/2199023255552),(-22133/68719476736)]
  L := [(2575421232261/576460752303423488),(6180916603279/3458764513820540928),(309028494905/1729382256910270464),(-420553/216172782113783808),(-10517/108086391056891904)]
  c := (643855308065/144115188075855872)
  R := (-615932471551373/100000000000000)
  total := (-17055817121/200000000000000)
  k := 18
  n := 32
  sFloor := (549749438909/1099511627776)
  nFloor := (103821588711/288230376151711744)
  eFloor := (187137555695/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=603851,width:=120770,den:=8589934592,localDen:=3458764513820540928,lowerC:=15452527393560,s:=[3458736660879507456,-11140968480768,-1113990365184],L:=[15452527393566,6180916603279,618056989810,-6728848,-336544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor252Source.source.poly i) 603851 120770 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor252Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 29) (CoreQuotient.fused G u 0 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 29 WideAnchor252Source.data
    WideAnchor252Source.path_checked WideAnchor252Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor252Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 0) (CoreQuotient.fused G u 29 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 0 WideAnchor252Source.data
    WideAnchor252Source.path_swapped WideAnchor252Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor252Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor252Cell054
