/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor511Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor511Cell065
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (560831/1073741824)
  b := (672997/1073741824)
  s := [(4396836539453/4398046511104),(-483674237/4398046511104),(-24096739/2199023255552)]
  L := [(11385606173196049057801743/79228162514264337593543950336),(2069905702099/36028797018963968),(309813506395/54043195528445952),(-5592413/2251799813685248),(-416263/3377699720527872)]
  c := (647196780687/4503599627370496)
  R := (-442386858032773/100000000000000)
  total := (-18093752077/40000000000000)
  k := 13
  n := 32
  sFloor := (2198152335869/4398046511104)
  nFloor := (996876667143/36028797018963968)
  eFloor := (954355066417/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=560831,width:=112166,den:=1073741824,localDen:=237684487542793012780631851008,lowerC:=34156818519578411978981376,s:=[237619096808274143214626144256,-26139301362262907629338624,-2604529554749858361901056],L:=[34156818519588147173405229,13655312327146173779410944,1362574210893426542510080,-590296619599263694848,-29291904557626949632],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor511Source.source.poly i) 560831 112166 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor511Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 41) (CoreQuotient.fused G u 4 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 41 WideAnchor511Source.data
    WideAnchor511Source.path_checked WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 4) (CoreQuotient.fused G u 41 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 4 WideAnchor511Source.data
    WideAnchor511Source.path_swapped WideAnchor511Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor511Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor511Cell065
