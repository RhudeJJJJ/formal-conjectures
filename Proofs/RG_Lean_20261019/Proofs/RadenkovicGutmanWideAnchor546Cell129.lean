/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor546Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor546Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5067062489801/2305843009213693952),(-5807520523447/4611686018427387904),(770010304715/2305843009213693952)]
  L := [(4724879189231974713465/4722366482869645213696),(-2793088829/13194139533312),(413717185/6597069766656),(-12678733/824633720832),(986435/412316860416)]
  c := (1099918583793/1099511627776)
  R := (18502793109/100000000000000)
  total := (2707640755019/1000000000000000)
  k := 0
  n := 32
  sFloor := (366664066599/576460752303423488)
  nFloor := 14230487552056065489283638959166782611598781054368409667769429930380010373602083324361834872716204861252476480950108160
  eFloor := 14222857192725647801013877189782566289069758124570251794295251385453052850358114945879061548429461881426248344327421952
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=14167099448608935641088,lowerC:=14172343036960711901184,s:=[31132031937337344,-17840703048029184,4730943312168960],L:=[14174637567695924140395,-2999056293844484096,888450889684090880,-217818974358863872,33893648517038080],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor546Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor546Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 24) (CoreQuotient.fused G u 5 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 24 WideAnchor546Source.data
    WideAnchor546Source.path_checked WideAnchor546Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor546Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 5) (CoreQuotient.fused G u 24 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 5 WideAnchor546Source.data
    WideAnchor546Source.path_swapped WideAnchor546Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor546Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor546Cell129
