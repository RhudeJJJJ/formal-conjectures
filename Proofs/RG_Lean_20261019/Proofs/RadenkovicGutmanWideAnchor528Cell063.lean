/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor528Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor528Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1557865/4294967296)
  b := (934719/2147483648)
  s := [(4398022984517/4398046511104),(-9410567/4398046511104),(-470511/2199023255552)]
  L := [(3454932832631/1152921504606846976),(43186503263/36028797018963968),(103646099233/864691128455135232),(-12571/36028797018963968),(-943/54043195528445952)]
  c := (1727466416315/576460752303423488)
  R := (-7948754188291/1250000000000)
  total := (-454506223737/1000000000000000)
  k := 19
  n := 32
  sFloor := (137437894779/274877906944)
  nFloor := (1309848888293/288230376151711744)
  eFloor := (584549903189/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1557865,width:=311573,den:=4294967296,localDen:=3458764513820540928,lowerC:=10364798497890,s:=[3458746011759673344,-7400771026944,-740049813504],L:=[10364798497893,4145904313248,414584396932,-1206816,-60352],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor528Source.source.poly i) 1557865 311573 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor528Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 8 WideAnchor528Source.data
    WideAnchor528Source.path_checked WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 4 WideAnchor528Source.data
    WideAnchor528Source.path_swapped WideAnchor528Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor528Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor528Cell063
