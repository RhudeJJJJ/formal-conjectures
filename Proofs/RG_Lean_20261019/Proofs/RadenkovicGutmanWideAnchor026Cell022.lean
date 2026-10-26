/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor026Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor026Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (904491/4398046511104)
  b := (1085389/4398046511104)
  s := [(2199023248441/2199023255552),(-5687/4398046511104),(-285/2199023255552)]
  L := [(1595155650121875235033103289/664613997892457936451903530140172288),(566712501359/590295810358705651712),(85006780081/885443715538058477568),(-9/36893488147419103232),(-1/55340232221128654848)]
  c := (354195706125/147573952589676412928)
  R := (-248096820725451/25000000000000)
  total := (-50540983/125000000000000)
  k := 29
  n := 32
  sFloor := (1073741819/2147483648)
  nFloor := (884728453993/151115727451828646838272)
  eFloor := (297982751305/75557863725914323419136)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=904491,width:=180898,den:=4398046511104,localDen:=1993841993677373809355710590420516864,lowerC:=4785466950362339123134464000,s:=[1993841987229870181895989544418803712,-2578185426055648543707758592,-258407893942626986093445120],L:=[4785466950365625705099309867,1914184657459945580997378048,191418251548378650889945088,-486388759756013568,-36028797018963968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor026Source.source.poly i) 904491 180898 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor026Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 35) (CoreQuotient.fused G u 9 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 35 WideAnchor026Source.data
    WideAnchor026Source.path_checked WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 9) (CoreQuotient.fused G u 35 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 9 WideAnchor026Source.data
    WideAnchor026Source.path_swapped WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor026Cell022
