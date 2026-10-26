/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor042Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor042Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(5866625065585/4611686018427387904),(-1681322214371/2305843009213693952),(222961708983/1152921504606846976)]
  L := [(18896457394572353102927/18889465931478580854784),(-972423799/6597069766656),(48064455/1099511627776),(-4423505/412316860416),(114805/68719476736)]
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
 left:=1199841,width:=239968,den:=16384,localDen:=56668397794435742564352,lowerC:=56682983060183873224704,s:=[72089088805908480,-41320174740381696,10959013919932416],L:=[56689372183717059308781,-8353056829114155008,2477223147900764160,-607961897878159360,94672074320117760],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor042Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor042Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 21) (CoreQuotient.fused G u 10 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 21 WideAnchor042Source.data
    WideAnchor042Source.path_checked WideAnchor042Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor042Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 10) (CoreQuotient.fused G u 21 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 10 WideAnchor042Source.data
    WideAnchor042Source.path_swapped WideAnchor042Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor042Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor042Cell130
