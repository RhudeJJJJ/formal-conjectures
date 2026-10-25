/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor255Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor255Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(2933859180617/2305843009213693952),(-6727295677751/9223372036854775808),(892196498935/4611686018427387904)]
  L := [(9448229348918184626807/9444732965739290427392),(-1945573487/13194139533312),(288564679/6597069766656),(-8854813/824633720832),(689585/412316860416)]
  c := (549897327907/549755813888)
  R := (2573793761/20000000000000)
  total := (2260300969579/1000000000000000)
  k := 0
  n := 32
  sFloor := (849066755323/2305843009213693952)
  nFloor := 367728650690520792511736358679480304931246583117378778962378278128747427136540212149215599076419504317803757254826910323283812476256256
  eFloor := 367591634182758795109528277201140237267725890092627359938142607193829350224347193134285523078920277220130962072034400771115478931210240
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=28334198897217871282176,lowerC:=28341492474220237553664,s:=[36051261611421696,-20666252322051072,5481655289456640],L:=[28344688046754553880421,-4178087249314840576,1239375859085737984,-304249057977565184,47387920364994560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor255Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor255Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 32) (CoreQuotient.fused G u 0 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 32 WideAnchor255Source.data
    WideAnchor255Source.path_checked WideAnchor255Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor255Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 0) (CoreQuotient.fused G u 32 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 0 WideAnchor255Source.data
    WideAnchor255Source.path_swapped WideAnchor255Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor255Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor255Cell130
