/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor545Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor545Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (435483/137438953472)
  b := (1045159/274877906944)
  s := [(4398042335541/4398046511104),(-835111/2199023255552),(-41755/1099511627776)]
  L := [(5772550167001/9223372036854775808),(2309015189761/9223372036854775808),(346350545237/13835058055282163712),(-11131/576460752303423488),(-833/864691128455135232)]
  c := (721568770875/1152921504606846976)
  R := (-714206865322533/100000000000000)
  total := (-7146567/1600000000000)
  k := 21
  n := 32
  sFloor := (2199020249149/4398046511104)
  nFloor := (483399468485/590295810358705651712)
  eFloor := (1466606419183/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=870966,width:=174193,den:=274877906944,localDen:=27670116110564327424,lowerC:=17317650501000,s:=[27670089840193437696,-10508128223232,-1050798981120],L:=[17317650501003,6927045569283,692701090474,-534288,-26656],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor545Source.source.poly i) 870966 174193 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor545Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 23) (CoreQuotient.fused G u 5 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 23 WideAnchor545Source.data
    WideAnchor545Source.path_checked WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 5) (CoreQuotient.fused G u 23 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 5 WideAnchor545Source.data
    WideAnchor545Source.path_swapped WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor545Cell037
