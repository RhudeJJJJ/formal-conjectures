/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor016Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor016Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5067062489801/2305843009213693952),(-5807520523447/4611686018427387904),(770010304715/2305843009213693952)]
  L := [(4724879189289677006903/4722366482869645213696),(-2793088829/13194139533312),(413717185/6597069766656),(-12678733/824633720832),(986435/412316860416)]
  c := (549959291903/549755813888)
  R := (185027937/1000000000000)
  total := (67691020739/25000000000000)
  k := 0
  n := 32
  sFloor := (366664066599/576460752303423488)
  nFloor := 10223829074094192086670652341712274494289097355544659789240485094251851461014325624307833064335578405137769511976055443110210361261817856
  eFloor := 10218347077120610625074179018618495961788833849042393218298861488663848554134802114394253029753123541601275159416753251881946247954694144
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=14167099448608935641088,lowerC:=14172343037128215625728,s:=[31132031937337344,-17840703048029184,4730943312168960],L:=[14174637567869031020709,-2999056293844484096,888450889684090880,-217818974358863872,33893648517038080],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor016Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor016Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 25) (CoreQuotient.fused G u 9 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 25 WideAnchor016Source.data
    WideAnchor016Source.path_checked WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 9) (CoreQuotient.fused G u 25 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 9 WideAnchor016Source.data
    WideAnchor016Source.path_swapped WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor016Cell129
