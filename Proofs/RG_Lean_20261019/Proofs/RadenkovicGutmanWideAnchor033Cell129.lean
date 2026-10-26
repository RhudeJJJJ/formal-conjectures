/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor033Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor033Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5067062489801/2305843009213693952),(-5807520523447/4611686018427387904),(770010304715/2305843009213693952)]
  L := [(9449758378237518575071/9444732965739290427392),(-2793088829/13194139533312),(413717185/6597069766656),(-12678733/824633720832),(986435/412316860416)]
  c := (1099918583767/1099511627776)
  R := (2312848991/12500000000000)
  total := (1353820304443/500000000000000)
  k := 0
  n := 32
  sFloor := (366664066599/576460752303423488)
  nFloor := 1426489105385901511138826577518465496811579205196039290338183603248453744620591637647178334208
  eFloor := 1425724224743039190217599537373835615532285330818500658370599496259544134461314422882844016640
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=28334198897217871282176,lowerC:=28344686073251408904192,s:=[62264063874674688,-35681406096058368,9461886624337920],L:=[28349275134712555725213,-5998112587688968192,1776901779368181760,-435637948717727744,67787297034076160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor033Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor033Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 12) (CoreQuotient.fused G u 10 12) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 12 WideAnchor033Source.data
    WideAnchor033Source.path_checked WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 10) (CoreQuotient.fused G u 12 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 12 10 WideAnchor033Source.data
    WideAnchor033Source.path_swapped WideAnchor033Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor033Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor033Cell129
