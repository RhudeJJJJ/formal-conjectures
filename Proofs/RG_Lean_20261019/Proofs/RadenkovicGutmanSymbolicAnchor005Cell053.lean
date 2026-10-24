/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor005Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (79997/137438953472)
  b := (1407947/2199023255552)
  s := [(4398046491385/4398046511104),(-3947/4398046511104),(-97/2199023255552)]
  L := [(194622752537088930421537251/83076749736557242056487941267521536),(276575132543/590295810358705651712),(13828734723/590295810358705651712),(1/73786976294838206464),(-1/36893488147419103232)]
  c := (86429864393/36893488147419103232)
  R := (-99359838153337/10000000000000)
  total := (-115102057/200000000000000)
  k := 29
  n := 32
  sFloor := (1099511621811/2199023255552)
  nFloor := (1439880271079/75557863725914323419136)
  eFloor := (43058120591/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1279952,width:=127995,den:=2199023255552,localDen:=83076749736557242056487941267521536,lowerC:=194622752536998650224574464,s:=[83076749364075863353661805392035840,-74556722031545958633832448,-3664556390706844685828096],L:=[194622752537088930421537251,38924489495643760680239104,1946221392047132475654144,1125899906842624,-2251799813685248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor005Source.source.poly i) 1279952 127995 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor005Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 14) (CoreQuotient.fused G u 9 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 14 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_checked SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 9) (CoreQuotient.fused G u 14 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 9 SymbolicAnchor005Source.data
    SymbolicAnchor005Source.path_swapped SymbolicAnchor005Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor005Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor005Cell053
