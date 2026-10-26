/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor263Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor263Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(1965674335441/4611686018427387904),(-4508070429005/18446744073709551616),(597964965109/9223372036854775808)]
  L := [(1180802885863253944931/1180591620717411303424),(-470856389/6597069766656),(34966565/1649267441664),(-1074341/206158430208),(20935/25769803776)]
  c := (549824191081/549755813888)
  R := (1554620691/25000000000000)
  total := (786572265737/500000000000000)
  k := 0
  n := 32
  sFloor := (142204901343/1152921504606846976)
  nFloor := 1941165664061180687644567600002666583892817877913331284343963927694591125973218998322505333263394332342271921545525769749477661190859839699681292461521308505520272708126900224
  eFloor := 1940816701578329281193078465082039077275888524288191268434553532514170343849012683437839653328295590286955013180586919612977563051739625272894679648746490210855556963117301760
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=3541774862152233910272,lowerC:=3542215378863824830464,s:=[1509637889618688,-865549522368960,229618546601856],L:=[3542408657589761834793,-252789098983456768,75090126564229120,-18457037839007744,2877284490936320],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor263Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor263Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 39) (CoreQuotient.fused G u 0 39) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 39 WideAnchor263Source.data
    WideAnchor263Source.path_checked WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 39 0) (CoreQuotient.fused G u 39 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 39 0 WideAnchor263Source.data
    WideAnchor263Source.path_swapped WideAnchor263Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor263Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor263Cell132
