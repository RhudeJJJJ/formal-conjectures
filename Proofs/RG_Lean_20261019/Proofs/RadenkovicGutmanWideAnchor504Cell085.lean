/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor504Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor504Cell085
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (671899/33554432)
  b := (1612557/67108864)
  s := [(947446099251/1099511627776),(-158921081917/4398046511104),(1705150251/1099511627776)]
  L := [(266284241734035221133/4722366482869645213696),(3551363248009/211106232532992),(12706079105/105553116266496),(-1513824943/13194139533312),(95478115/6597069766656)]
  c := (991986102365/17592186044416)
  R := (-71887525255429/50000000000000)
  total := (-5484877961979/1000000000000000)
  k := 5
  n := 32
  sFloor := (1818841958045/4398046511104)
  nFloor := (30618196795/1099511627776)
  eFloor := (322704995881/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1343798,width:=268759,den:=67108864,localDen:=14167099448608935641088,lowerC:=798852725202034360320,s:=[12207750033017445285888,-511920637108838989824,21970693688433573888],L:=[798852725202105663399,238327953225234251776,1705381069261373440,-1625457155513516032,205037690704363520],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor504Source.source.poly i) 1343798 268759 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor504Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 34) (CoreQuotient.fused G u 4 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 34 WideAnchor504Source.data
    WideAnchor504Source.path_checked WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 4) (CoreQuotient.fused G u 34 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 4 WideAnchor504Source.data
    WideAnchor504Source.path_swapped WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor504Cell085
