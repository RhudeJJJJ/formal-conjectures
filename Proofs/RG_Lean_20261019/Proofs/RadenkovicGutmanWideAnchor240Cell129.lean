/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor240Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor240Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(5068421931737/2305843009213693952),(-726251922863/576460752303423488),(192611235083/576460752303423488)]
  L := [(295304991467610033987/295147905179352825856),(-698647609/3298534883328),(207042557/3298534883328),(-3173717/206158430208),(493999/206158430208)]
  c := (1099918659621/1099511627776)
  R := (4626560023/25000000000000)
  total := (541650553017/200000000000000)
  k := 0
  n := 32
  sFloor := (366732397577/576460752303423488)
  nFloor := 1426489310672314425599572837858889075437307339390258473515370503030429466527060725174330458112
  eFloor := 1425724224743039190217599537373835615532285330818500658370599496259544134461314422882844016640
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=885443715538058477568,lowerC:=885771500874815766528,s:=[1946274021787008,-1115522953517568,295850857087488],L:=[885914974402830101961,-187541789505224704,55577563199700992,-13631010721759232,2121709549256704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor240Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor240Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 22) (CoreQuotient.fused G u 0 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 22 WideAnchor240Source.data
    WideAnchor240Source.path_checked WideAnchor240Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor240Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 0) (CoreQuotient.fused G u 22 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 0 WideAnchor240Source.data
    WideAnchor240Source.path_swapped WideAnchor240Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor240Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor240Cell129
