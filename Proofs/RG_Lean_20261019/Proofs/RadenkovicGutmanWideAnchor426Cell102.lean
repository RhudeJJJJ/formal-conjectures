/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor426Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor426Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (931671/2097152)
  b := (1118005/2097152)
  s := [(4663135221105/17592186044416),(-948945178473/17592186044416),(65125468135/8796093022208)]
  L := [(112732191833192057625/147573952589676412928),(1544017396147/13194139533312),(-35620670163/2199023255552),(1260328985/824633720832),(-9991685/137438953472)]
  c := (839920281121/1099511627776)
  R := (-3366430019313/25000000000000)
  total := (-4493708251459/500000000000000)
  k := 1
  n := 32
  sFloor := (1922220489451/17592186044416)
  nFloor := (28761777091/268435456)
  eFloor := (699938996977/8589934592)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=931671,width:=186334,den:=2097152,localDen:=442721857769029238784,lowerC:=338196575499545739264,s:=[117351640262529515520,-23880987347100106752,3277872138006036480],L:=[338196575499576172875,51808626725831573504,-7171388128672874496,676633971596984320,-32185470230200320],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor426Source.source.poly i) 931671 186334 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor426Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 6 WideAnchor426Source.data
    WideAnchor426Source.path_checked WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 6 2 WideAnchor426Source.data
    WideAnchor426Source.path_swapped WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor426Cell102
