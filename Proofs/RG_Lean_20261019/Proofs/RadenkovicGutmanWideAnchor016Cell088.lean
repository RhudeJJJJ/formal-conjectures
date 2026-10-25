/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor016Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor016Cell088
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (72565/2097152)
  b := (43539/1048576)
  s := [(5912789150835/35184372088832),(5102671327/17592186044416),(21324910967/8796093022208)]
  L := [(147766147968672093383/147573952589676412928),(-216472307483/13194139533312),(-47769834043/6597069766656),(1355269505/824633720832),(-76379393/412316860416)]
  c := (2153091889197/2199023255552)
  R := (-131927437183/12500000000000)
  total := (-31149403803/1000000000000000)
  k := 1
  n := 32
  sFloor := (369549321927/4398046511104)
  nFloor := (718054038281/4398046511104)
  eFloor := (127692749835/1099511627776)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=72565,width:=14513,den:=2097152,localDen:=442721857769029238784,lowerC:=433474652314873626624,s:=[74400105559511531520,128412928545128448,1073317912422383616],L:=[443298443906016280149,-7263605321321414656,-3205779296094257152,727604775155138560,-82011748755832832],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor016Source.source.poly i) 72565 14513 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor016Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 25) (CoreQuotient.fused G u 9 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 25 WideAnchor016Source.data
    WideAnchor016Source.path_checked WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 9) (CoreQuotient.fused G u 25 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 9 WideAnchor016Source.data
    WideAnchor016Source.path_swapped WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor016Cell088
