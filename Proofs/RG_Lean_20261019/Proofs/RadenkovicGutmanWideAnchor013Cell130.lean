/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor013Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor013Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(5866625065585/4611686018427387904),(-1681322214371/2305843009213693952),(222961708983/1152921504606846976)]
  L := [(9448228697286176551463/9444732965739290427392),(-972423799/6597069766656),(48064455/1099511627776),(-4423505/412316860416),(114805/68719476736)]
  c := (1099794619177/1099511627776)
  R := (514692127/4000000000000)
  total := (2259946064137/1000000000000000)
  k := 0
  n := 32
  sFloor := (1697913736387/4611686018427387904)
  nFloor := 68542175743542823934715341190854060390243462137477026844512440065252514420434246142659886975832469925447562818841008144417420214272
  eFloor := 68516641535369265957695752315478635048505415597329383278540255833645398841087913986043240283788903305301144629053341067676953346048
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=28334198897217871282176,lowerC:=28341491530091936612352,s:=[36044544402954240,-20660087370190848,5479506959966208],L:=[28344686091858529654389,-4176528414557077504,1238611573950382080,-303980948939079680,47336037160058880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor013Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor013Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 22) (CoreQuotient.fused G u 9 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 22 WideAnchor013Source.data
    WideAnchor013Source.path_checked WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 9) (CoreQuotient.fused G u 22 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 9 WideAnchor013Source.data
    WideAnchor013Source.path_swapped WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor013Cell130
