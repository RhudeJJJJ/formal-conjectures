/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor497Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor497Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (838683/17179869184)
  b := (1006419/17179869184)
  s := [(4398027415375/4398046511104),(-7638199/4398046511104),(-381889/2199023255552)]
  L := [(5375072274999/2305843009213693952),(6450018462961/6917529027641081856),(107496910231/1152921504606846976),(-225967/432345564227567616),(-1883/72057594037927936)]
  c := (1343768068749/576460752303423488)
  R := (-20264351371553/3125000000000)
  total := (-31198650417/500000000000000)
  k := 19
  n := 32
  sFloor := (2199009506699/4398046511104)
  nFloor := (205445411275/1152921504606846976)
  eFloor := (382665437403/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=838683,width:=167736,den:=17179869184,localDen:=6917529027641081856,lowerC:=16125216824988,s:=[6917498992656384000,-12013848231936,-1201318920192],L:=[16125216824997,6450018462961,644981461386,-3615472,-180768],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor497Source.source.poly i) 838683 167736 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor497Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 27) (CoreQuotient.fused G u 4 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 27 WideAnchor497Source.data
    WideAnchor497Source.path_checked WideAnchor497Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor497Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 4) (CoreQuotient.fused G u 27 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 4 WideAnchor497Source.data
    WideAnchor497Source.path_swapped WideAnchor497Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor497Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor497Cell052
