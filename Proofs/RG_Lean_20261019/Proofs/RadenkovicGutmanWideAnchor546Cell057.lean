/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor546Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor546Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (521727/4294967296)
  b := (78259/536870912)
  s := [(4395218413983/4398046511104),(-1130170027/4398046511104),(-56213385/2199023255552)]
  L := [(3314485381143383526480807/9903520314283042199192993792),(7230002672179/54043195528445952),(360542315215/27021597764222976),(-23874565/3377699720527872),(-590371/1688849860263936)]
  c := (753626723313/2251799813685248)
  R := (-200058579702639/50000000000000)
  total := (-94931815901/1000000000000000)
  k := 12
  n := 32
  sFloor := (2196987908593/4398046511104)
  nFloor := (581475071597/576460752303423488)
  eFloor := (1117580324463/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=521727,width:=104345,den:=4294967296,localDen:=29710560942849126597578981376,lowerC:=9943456143424437570502656,s:=[29691456017138671838772068352,-7634749968693755104985088,-759487739217702687866880],L:=[9943456143430150579442421,3974736003456180999421952,396420467884172341411840,-210002894604751339520,-10385916467227918336],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor546Source.source.poly i) 521727 104345 4294967296
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
end Gebendorfer.RadenkovicGutman.WideAnchor546Cell057
