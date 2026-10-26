/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor516Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor516Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (78259/536870912)
  b := (375643/2147483648)
  s := [(1099511067205/1099511627776),(-224227/1099511627776),(-22423/1099511627776)]
  L := [(2396202786773/9223372036854775808),(5750867183105/55340232221128654848),(287542213787/27670116110564327424),(-5663/3458764513820540928),(-143/1729382256910270464)]
  c := (599050696693/2305843009213693952)
  R := (-758168297356431/100000000000000)
  total := (-218301143777/1000000000000000)
  k := 22
  n := 32
  sFloor := (1099510820555/2199023255552)
  nFloor := (278909540709/576460752303423488)
  eFloor := (1094687742155/2305843009213693952)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=313036,width:=62607,den:=2147483648,localDen:=55340232221128654848,lowerC:=14377216720632,s:=[55340204006666403840,-11285714436096,-1128586543104],L:=[14377216720638,5750867183105,575084427574,-90608,-4576],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor516Source.source.poly i) 313036 62607 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor516Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_checked WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((25/13) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (25/13) 4 4 WideAnchor516Source.data
    WideAnchor516Source.path_swapped WideAnchor516Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor516Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor516Cell058
