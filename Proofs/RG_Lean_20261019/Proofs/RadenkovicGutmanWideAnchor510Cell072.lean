/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor510Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor510Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (502389/268435456)
  b := (1205733/536870912)
  s := [(4381244140759/4398046511104),(-831752531/549755813888),(-157243419/1099511627776)]
  L := [(6554239639518726739943/4835703278458516698824704),(1816810240193/3377699720527872),(87982558745/1688849860263936),(-70263803/211106232532992),(-1551185/105553116266496)]
  c := (763013916965/562949953421312)
  R := (-165091743489399/50000000000000)
  total := (-48045128809/40000000000000)
  k := 10
  n := 32
  sFloor := (2186980573417/4398046511104)
  nFloor := (1043095953035/4503599627370496)
  eFloor := (368224535257/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1004778,width:=200955,den:=536870912,localDen:=14507109835375550096474112,lowerC:=19662718918545207459840,s:=[14451686630669971674365952,-21948517902398829625344,-2074691610981043273728],L:=[19662718918556180219829,7803140564666839728128,755764424856347607040,-4828491775641387008,-213193243041464320],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor510Source.source.poly i) 1004778 200955 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor510Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 40) (CoreQuotient.fused G u 4 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 40 WideAnchor510Source.data
    WideAnchor510Source.path_checked WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 4) (CoreQuotient.fused G u 40 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 4 WideAnchor510Source.data
    WideAnchor510Source.path_swapped WideAnchor510Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor510Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor510Cell072
