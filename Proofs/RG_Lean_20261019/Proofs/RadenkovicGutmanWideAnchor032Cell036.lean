/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor032Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor032Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1451611/549755813888)
  b := (435483/137438953472)
  s := [(4398046238627/4398046511104),(-108987/4398046511104),(-5451/2199023255552)]
  L := [(4804354242475/147573952589676412928),(5765200854965/442721857769029238784),(96086256673/73786976294838206464),(-2033/27670116110564327424),(-17/4611686018427387904)]
  c := (600544280309/18446744073709551616)
  R := (-107751983381393/12500000000000)
  total := (-4502727627/1000000000000000)
  k := 25
  n := 32
  sFloor := (2199023059369/4398046511104)
  nFloor := (862663612277/2361183241434822606848)
  eFloor := (820833128237/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1451611,width:=290321,den:=549755813888,localDen:=442721857769029238784,lowerC:=14413062727416,s:=[442721830340596334592,-10970990641152,-1097431252992],L:=[14413062727425,5765200854965,576517540038,-32528,-1632],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor032Source.source.poly i) 1451611 290321 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor032Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 11) (CoreQuotient.fused G u 10 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 11 WideAnchor032Source.data
    WideAnchor032Source.path_checked WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 10) (CoreQuotient.fused G u 11 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 10 WideAnchor032Source.data
    WideAnchor032Source.path_swapped WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor032Cell036
