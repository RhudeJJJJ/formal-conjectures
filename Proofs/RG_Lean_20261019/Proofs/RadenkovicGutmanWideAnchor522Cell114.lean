/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor522Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor522Cell114
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (259589/65536)
  b := (1246027/262144)
  s := [(3589274387901/562949953421312),(-1798757842865/562949953421312),(53239337869/70368744177664)]
  L := [(642392883071941899833/590295810358705651712),(-165824735053/6597069766656),(14896938467/3298534883328),(-210720299/412316860416),(4258633/206158430208)]
  c := (1173338969779/1099511627776)
  R := (259949593/8000000000)
  total := (7350450932527/250000000000000)
  k := 0
  n := 32
  sFloor := (554107811997/281474976710656)
  nFloor := 550354031781347328
  eFloor := 499313226435526656
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1038356,width:=207671,den:=262144,localDen:=1770887431076116955136,lowerC:=1889794688371176505344,s:=[11290880941703036928,-5658402911520030720,1339811806687789056],L:=[1927178649215825699499,-44513238370031239168,7997732940786171904,-905036792808341504,36581378921332736],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor522Source.source.poly i) 1038356 207671 262144
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
end Gebendorfer.RadenkovicGutman.WideAnchor522Cell114
