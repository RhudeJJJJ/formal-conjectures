/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor504Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor504Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5067062489801/2305843009213693952),(-5807520523447/4611686018427387904),(770010304715/2305843009213693952)]
  L := [(9449758378648318509393/9444732965739290427392),(-2793088829/13194139533312),(413717185/6597069766656),(-12678733/824633720832),(986435/412316860416)]
  c := (549959291907/549755813888)
  R := (1156424629/6250000000000)
  total := (1353820437071/500000000000000)
  k := 0
  n := 32
  sFloor := (366664066599/576460752303423488)
  nFloor := 1971190604737980467852212511279878245829656859837543502775692307132206693828890761781588206434161900063730119880748362481500255183382214897122425176064
  eFloor := 1970133656225339400119693362086603594556435227030133116949126462867590675310557777611209516355024095794259497944006229840968885957559017392373084717056
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=28334198897217871282176,lowerC:=28344686074462589681664,s:=[62264063874674688,-35681406096058368,9461886624337920],L:=[28349275135944955528179,-5998112587688968192,1776901779368181760,-435637948717727744,67787297034076160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor504Source.source.poly i) 999868 199973 16384
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
end Gebendorfer.RadenkovicGutman.WideAnchor504Cell129
