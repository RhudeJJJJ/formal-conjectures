/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor482Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor482Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5066897948039/2305843009213693952),(-5807218645321/4611686018427387904),(769957725209/2305843009213693952)]
  L := [(4724879019824695349463/4722366482869645213696),(-2792711935/13194139533312),(137874927/2199023255552),(-12674681/824633720832),(328681/137438953472)]
  c := (549959282357/549755813888)
  R := (9250962909/50000000000000)
  total := (2707486906301/1000000000000000)
  k := 0
  n := 32
  sFloor := (1466623175293/2305843009213693952)
  nFloor := 532843224558123879399865617076970773903699287478628283016390223843033088
  eFloor := 532557534211785688958132630829266332538523234859911195543240830483431424
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=14167099448608935641088,lowerC:=14172342791129668780032,s:=[31131020992751616,-17839775678426112,4730620263684096],L:=[14174637059474086048389,-2998651606993469440,888252453605081088,-217749361528930304,33880179499597824],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor482Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor482Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 12) (CoreQuotient.fused G u 4 12) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 12 WideAnchor482Source.data
    WideAnchor482Source.path_checked WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 4) (CoreQuotient.fused G u 12 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 12 4 WideAnchor482Source.data
    WideAnchor482Source.path_swapped WideAnchor482Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor482Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor482Cell129
