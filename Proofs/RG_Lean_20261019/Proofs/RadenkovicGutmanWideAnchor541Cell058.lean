/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor541Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor541Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (78259/536870912)
  b := (375643/2147483648)
  s := [(4389489088921/4398046511104),(-3413302165/4398046511104),(-168000159/2199023255552)]
  L := [(394654097875143585148455/309485009821345068724781056),(3438965946859/6755399441055744),(170589760673/3377699720527872),(-8448847/105553116266496),(-817403/211106232532992)]
  c := (1435743244201/1125899906842624)
  R := (-166616381418303/50000000000000)
  total := (-94422964881/1000000000000000)
  k := 10
  n := 32
  sFloor := (2192869893219/4398046511104)
  nFloor := (867425391099/576460752303423488)
  eFloor := (331208136961/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=313036,width:=62607,den:=2147483648,localDen:=928455029464035206174343168,lowerC:=1183962293624877436895232,s:=[926648504306787824154181632,-720569360549855027527680,-70931761262867257491456],L:=[1183962293625430755445365,472647880762146525544448,46891356359872124813312,-74316844142402994176,-3594976412315942912],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor541Source.source.poly i) 313036 62607 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor541Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 19) (CoreQuotient.fused G u 5 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 19 WideAnchor541Source.data
    WideAnchor541Source.path_checked WideAnchor541Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor541Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 5) (CoreQuotient.fused G u 19 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 5 WideAnchor541Source.data
    WideAnchor541Source.path_swapped WideAnchor541Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor541Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor541Cell058
