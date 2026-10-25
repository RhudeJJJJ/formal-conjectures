/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor505Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor505Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (538283/65536)
  b := (1291879/131072)
  s := [(3833032980499/4503599627370496),(-2122776124027/4503599627370496),(136751806293/1125899906842624)]
  L := [(302931256385671692087/295147905179352825856),(-42396235937/4398046511104),(5647826653/2199023255552),(-154158847/274877906944),(10904939/137438953472)]
  c := (280050582245/274877906944)
  R := (466080334933/50000000000000)
  total := (9049678978661/500000000000000)
  k := 0
  n := 32
  sFloor := (564316020411/2251799813685248)
  nFloor := 31032814016246408948124028312329544651355550464454288805066754974746383275261952
  eFloor := 30184048840599177621605349763736501970952339679665161916704977372145591991140352
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1076566,width:=215313,den:=131072,localDen:=295147905179352825856,lowerC:=300702022992008314880,s:=[251201649409982464,-139118256064233472,35848665508872192],L:=[302931256385671692087,-2845163231608045568,758038461503504384,-165526801563516928,23418178184937472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor505Source.source.poly i) 1076566 215313 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor505Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 35) (CoreQuotient.fused G u 4 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 35 WideAnchor505Source.data
    WideAnchor505Source.path_checked WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 4) (CoreQuotient.fused G u 35 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 4 WideAnchor505Source.data
    WideAnchor505Source.path_swapped WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor505Cell118
