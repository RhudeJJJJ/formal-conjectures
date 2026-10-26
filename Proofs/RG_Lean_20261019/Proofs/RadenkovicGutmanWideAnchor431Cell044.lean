/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor431Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor431Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (780205/68719476736)
  b := (468123/34359738368)
  s := [(2199023245591/2199023255552),(-3985/2199023255552),(-199/1099511627776)]
  L := [(2360031330559/1180591620717411303424),(944012529887/1180591620717411303424),(11800156509/147573952589676412928),(-13/73786976294838206464)]
  c := (1180015665279/590295810358705651712)
  R := (-1001530331432903/100000000000000)
  total := (-22528865343/1000000000000000)
  k := 29
  n := 32
  sFloor := (274877905151/549755813888)
  nFloor := (1745920488127/590295810358705651712)
  eFloor := (989034232265/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=780205,width:=156041,den:=68719476736,localDen:=1180591620717411303424,lowerC:=2360031330558,s:=[1180591615369640148992,-2139430584320,-213674622976],L:=[2360031330559,944012529887,94401252072,-208],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor431Source.source.poly i) 780205 156041 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor431Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 2 8 WideAnchor431Source.data
    WideAnchor431Source.path_checked WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 8 2 WideAnchor431Source.data
    WideAnchor431Source.path_swapped WideAnchor431Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor431Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor431Cell044
