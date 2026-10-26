/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor515Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor515Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (775127/65536)
  b := (116269/8192)
  s := [(330624156021/1125899906842624),(-5963752346577/36028797018963968),(779871248409/18014398509481984)]
  L := [(598168634356248205697/590295810358705651712),(-22325583307/4398046511104),(3134969279/2199023255552),(-90852379/274877906944),(6764557/137438953472)]
  c := (554926350479/549755813888)
  R := (468059910483/100000000000000)
  total := (1646750587403/125000000000000)
  k := 0
  n := 32
  sFloor := (24124856027/281474976710656)
  nFloor := 133010660681371363389210624
  eFloor := 131182962168612991409324032
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=775127,width:=155025,den:=65536,localDen:=590295810358705651712,lowerC:=595847631748984733696,s:=[173342277511938048,-97710118446317568,25554821067866112],L:=[598168634356248205697,-2996489067740266496,841536907954356224,-195103998284398592,29053551086927872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor515Source.source.poly i) 775127 155025 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor515Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_checked WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_swapped WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor515Cell120
