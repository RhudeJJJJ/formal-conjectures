/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor508Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor508Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (538283/65536)
  b := (1291879/131072)
  s := [(3833032980499/4503599627370496),(-2122776124027/4503599627370496),(136751806293/1125899906842624)]
  L := [(302931256417078926673/295147905179352825856),(-42396235937/4398046511104),(5647826653/2199023255552),(-154158847/274877906944),(10904939/137438953472)]
  c := (1120202329097/1099511627776)
  R := (932160675089/100000000000000)
  total := (18099358042831/1000000000000000)
  k := 0
  n := 32
  sFloor := (564316020411/2251799813685248)
  nFloor := 10395028226673019209703383699634601723455873916510043126247022605027658663974095814656
  eFloor := 10110718271606283634299817293923785932502172414493884139885723241343319991760931782656
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1076566,width:=215313,den:=131072,localDen:=295147905179352825856,lowerC:=300702023023415263232,s:=[251201649409982464,-139118256064233472,35848665508872192],L:=[302931256417078926673,-2845163231608045568,758038461503504384,-165526801563516928,23418178184937472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor508Source.source.poly i) 1076566 215313 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor508Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 38) (CoreQuotient.fused G u 4 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 38 WideAnchor508Source.data
    WideAnchor508Source.path_checked WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 4) (CoreQuotient.fused G u 38 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 4 WideAnchor508Source.data
    WideAnchor508Source.path_swapped WideAnchor508Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor508Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor508Cell118
