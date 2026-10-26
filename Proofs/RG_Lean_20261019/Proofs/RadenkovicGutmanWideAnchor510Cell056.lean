/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor510Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor510Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (869545/8589934592)
  b := (521727/4294967296)
  s := [(4397996840909/4398046511104),(-9933747/2199023255552),(-248303/549755813888)]
  L := [(4607788381673/1152921504606846976),(5529217432027/3458764513820540928),(276435147031/1729382256910270464),(-643069/216172782113783808),(-16075/108086391056891904)]
  c := (575973547709/144115188075855872)
  R := (-621503085972273/100000000000000)
  total := (-123929850497/1000000000000000)
  k := 18
  n := 32
  sFloor := (2198987493495/4398046511104)
  nFloor := (779673471885/1152921504606846976)
  eFloor := (275402879365/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=869545,width:=173909,den:=8589934592,localDen:=3458764513820540928,lowerC:=13823365145016,s:=[3458725451589746688,-15624433041408,-1562187399168],L:=[13823365145019,5529217432027,552870294062,-10289104,-514400],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor510Source.source.poly i) 869545 173909 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor510Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 40) (CoreQuotient.fused G u 4 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 40 WideAnchor510Source.data
    WideAnchor510Source.path_checked WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 4) (CoreQuotient.fused G u 40 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 4 WideAnchor510Source.data
    WideAnchor510Source.path_swapped WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor510Cell056
