/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor263Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor263Cell082
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (388831/33554432)
  b := (466597/33554432)
  s := [(982144217877/1099511627776),(-69677907359/2199023255552),(37264795/68719476736)]
  L := [(4728539383579217509139/75557863725914323419136),(4138661521379/211106232532992),(28608656405/105553116266496),(-2498952437/13194139533312),(95668231/6597069766656)]
  c := (1100948868221/17592186044416)
  R := (-27712824132631/20000000000000)
  total := (-121828515421/40000000000000)
  k := 4
  n := 32
  sFloor := (1895803001835/4398046511104)
  nFloor := (466157887805/35184372088832)
  eFloor := (209987909909/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=388831,width:=77766,den:=33554432,localDen:=226673591177742970257408,lowerC:=14185618150732226101248,s:=[202477310195386250428416,-7182344000654945550336,122919226227566837760],L:=[14185618150737652527417,4443853970884102455296,61436621820987965440,-42931675964698001408,3287135387289387008],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor263Source.source.poly i) 388831 77766 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor263Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 39) (CoreQuotient.fused G u 0 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 39 WideAnchor263Source.data
    WideAnchor263Source.path_checked WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 0) (CoreQuotient.fused G u 39 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 0 WideAnchor263Source.data
    WideAnchor263Source.path_swapped WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor263Cell082
