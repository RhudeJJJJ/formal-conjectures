/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor247Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor247Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1397805/34359738368)
  b := (838683/17179869184)
  s := [(1099511609865/1099511627776),(-28657/4398046511104),(-1433/2199023255552)]
  L := [(2595342120335/147573952589676412928),(519068416909/73786976294838206464),(155720516489/221360928884514619392),(-9/1152921504606846976),(-5/13835058055282163712)]
  c := (1297671060167/73786976294838206464)
  R := (-446403040884521/50000000000000)
  total := (-3593935501/50000000000000)
  k := 26
  n := 32
  sFloor := (17179868781/34359738368)
  nFloor := (95163189175/2305843009213693952)
  eFloor := (705167130111/36893488147419103232)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1397805,width:=279561,den:=34359738368,localDen:=442721857769029238784,lowerC:=7786026361002,s:=[442721850557108060160,-2884708073472,-288501006336],L:=[7786026361005,3114410501454,311441032978,-3456,-160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor247Source.source.poly i) 1397805 279561 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor247Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 2 WideAnchor247Source.data
    WideAnchor247Source.path_checked WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 2 0 WideAnchor247Source.data
    WideAnchor247Source.path_swapped WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor247Cell051
