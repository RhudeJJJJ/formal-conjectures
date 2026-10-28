/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor512Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor512Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (538283/65536)
  b := (1291879/131072)
  s := [(7666065960999/9007199254740992),(-4245552248057/9007199254740992),(547007225173/4503599627370496)]
  L := [(302931256458254910431/295147905179352825856),(-42396235937/4398046511104),(5647826653/2199023255552),(-154158847/274877906944),(10904939/137438953472)]
  c := (1120202329251/1099511627776)
  R := (466080340981/50000000000000)
  total := (4524839538727/250000000000000)
  k := 0
  n := 32
  sFloor := (564316020411/2251799813685248)
  nFloor := 241823419883897932756294934016795525231404226908074807936240100052543688125744251966240849920
  eFloor := 235209411327003648930040689066749854941066865649285591489706367031188244409456364435678429184
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1076566,width:=215313,den:=131072,localDen:=295147905179352825856,lowerC:=300702023064754323456,s:=[251201649410015232,-139118256064331776,35848665508937728],L:=[302931256458254910431,-2845163231608045568,758038461503504384,-165526801563516928,23418178184937472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor512Source.source.poly i) 1076566 215313 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor512Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 42) (CoreQuotient.fused G u 4 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 42 WideAnchor512Source.data
    WideAnchor512Source.path_checked WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 4) (CoreQuotient.fused G u 42 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 4 WideAnchor512Source.data
    WideAnchor512Source.path_swapped WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor512Cell118
