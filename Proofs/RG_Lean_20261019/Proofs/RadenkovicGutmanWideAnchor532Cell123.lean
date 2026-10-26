/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor532Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor532Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (669709/32768)
  b := (1607301/65536)
  s := [(4179498748961/72057594037927936),(-2382776660935/72057594037927936),(314565585223/36028797018963968)]
  L := [(593028818841230085431/590295810358705651712),(-2988435397/1649267441664),(36194321/68719476736),(-26117899/206158430208),(83455/4294967296)]
  c := (551535570329/549755813888)
  R := (161606457281/100000000000000)
  total := (7897455639843/1000000000000000)
  k := 0
  n := 32
  sFloor := (303231657309/18014398509481984)
  nFloor := 137059288643367668332457274037923366797383219281920
  eFloor := 136411815202880616499204346787721040949502118199296
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1339418,width:=267883,den:=65536,localDen:=1770887431076116955136,lowerC:=1776620427857822220288,s:=[102715361254465536,-58559119219138560,15461527644880896],L:=[1779086456523690256293,-3208808074080944128,932720549975556096,-224351044090462208,34409903586017280],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor532Source.source.poly i) 1339418 267883 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor532Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 10) (CoreQuotient.fused G u 5 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 10 WideAnchor532Source.data
    WideAnchor532Source.path_checked WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 5) (CoreQuotient.fused G u 10 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 5 WideAnchor532Source.data
    WideAnchor532Source.path_swapped WideAnchor532Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor532Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor532Cell123
