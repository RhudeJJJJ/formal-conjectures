/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor522Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor522Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(3777894605551/576460752303423488),(-2163390802449/576460752303423488),(35833045961/36028797018963968)]
  L := [(4727551813442742068391/4722366482869645213696),(-5746531729/13194139533312),(848321347/6597069766656),(-25912217/824633720832),(2011169/412316860416)]
  c := (275088063593/274877906944)
  R := (19106332981/50000000000000)
  total := (194063438223/50000000000000)
  k := 0
  n := 32
  sFloor := (1093916269239/576460752303423488)
  nFloor := 7383715328458884325888919020782489726758158336
  eFloor := 7375519926343662607070897802207827424100483072
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=14167099448608935641088,lowerC:=14177930839822839054336,s:=[92845537826021376,-53167492360986624,14090127000600576],L:=[14182655440328226205173,-6170291460370333696,1821756220931833856,-445168498327420928,69103240653832192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor522Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor522Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 4 6 WideAnchor522Source.data
    WideAnchor522Source.path_checked WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((23/12) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (23/12) 6 4 WideAnchor522Source.data
    WideAnchor522Source.path_swapped WideAnchor522Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor522Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor522Cell127
