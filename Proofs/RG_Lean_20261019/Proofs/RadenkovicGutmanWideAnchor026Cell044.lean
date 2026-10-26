/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor026Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor026Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (780205/68719476736)
  b := (468123/34359738368)
  s := [(4398003170307/4398046511104),(-4334017/1099511627776),(-433367/1099511627776)]
  L := [(296720551272553109419244503/40564819207303340847894502572032),(5059931815019/1729382256910270464),(252986319113/864691128455135232),(-256805/108086391056891904),(-6413/54043195528445952)]
  c := (1054163161287/144115188075855872)
  R := (-147820261698371/25000000000000)
  total := (-13213356119/1000000000000000)
  k := 18
  n := 32
  sFloor := (2198992050385/4398046511104)
  nFloor := (658292597271/36893488147419103232)
  eFloor := (886870271857/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=780205,width:=156041,den:=68719476736,localDen:=121694457621910022543683507716096,lowerC:=890161653817469488978722816,s:=[121693258377024708145613182599168,-479691014460638698596728832,-47965260833947723531026432],L:=[890161653817659328257733509,356061047447495092119535616,35604659140223130941784064,-289136725576720056320,-14440792205163495424],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor026Source.source.poly i) 780205 156041 68719476736
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
end Gebendorfer.RadenkovicGutman.WideAnchor026Cell044
