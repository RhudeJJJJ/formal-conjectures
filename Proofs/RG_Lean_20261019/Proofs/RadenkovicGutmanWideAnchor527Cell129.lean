/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor527Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor527Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5067062489801/2305843009213693952),(-5807520523447/4611686018427387904),(770010304715/2305843009213693952)]
  L := [(9449758377445624652415/9444732965739290427392),(-2793088829/13194139533312),(413717185/6597069766656),(-12678733/824633720832),(986435/412316860416)]
  c := (549959291837/549755813888)
  R := (185027877/1000000000000)
  total := (1353820048691/500000000000000)
  k := 0
  n := 32
  sFloor := (366664066599/576460752303423488)
  nFloor := 741655289034220301108395777828463035717742124546916352
  eFloor := 741257614932245929599333408586593300129642795881201664
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=28334198897217871282176,lowerC:=28344686070854817153024,s:=[62264063874674688,-35681406096058368,9461886624337920],L:=[28349275132336873957245,-5998112587688968192,1776901779368181760,-435637948717727744,67787297034076160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor527Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor527Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 7) (CoreQuotient.fused G u 4 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 7 WideAnchor527Source.data
    WideAnchor527Source.path_checked WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 4) (CoreQuotient.fused G u 7 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 4 WideAnchor527Source.data
    WideAnchor527Source.path_swapped WideAnchor527Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor527Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor527Cell129
