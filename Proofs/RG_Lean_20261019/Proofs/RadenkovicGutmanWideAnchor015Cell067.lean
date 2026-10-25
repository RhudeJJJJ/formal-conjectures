/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor015Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor015Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (201899/268435456)
  b := (969115/1073741824)
  s := [(4357600829809/4398046511104),(-15954315199/4398046511104),(-737324349/2199023255552)]
  L := [(11805638333473395182043/2417851639229258349412352),(2177284340039/1125899906842624),(313739035303/1688849860263936),(-104722241/70368744177664),(-6622075/105553116266496)]
  c := (1374357185963/281474976710656)
  R := (-133051435756521/50000000000000)
  total := (-24146557399/62500000000000)
  k := 8
  n := 32
  sFloor := (542521483239/1099511627776)
  nFloor := (1585244924531/36028797018963968)
  eFloor := (749877709689/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=807596,width:=161519,den:=1073741824,localDen:=7253554917687775048237056,lowerC:=35416915000402051596288,s:=[7186849172372012899762176,-26312932611755801051136,-2432090085503608553472],L:=[35416915000420185546129,14027047551840672546816,1347498896104974450688,-10794686406211928064,-455065528906547200],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor015Source.source.poly i) 807596 161519 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor015Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 24) (CoreQuotient.fused G u 9 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 24 WideAnchor015Source.data
    WideAnchor015Source.path_checked WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 9) (CoreQuotient.fused G u 24 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 9 WideAnchor015Source.data
    WideAnchor015Source.path_swapped WideAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor015Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor015Cell067
