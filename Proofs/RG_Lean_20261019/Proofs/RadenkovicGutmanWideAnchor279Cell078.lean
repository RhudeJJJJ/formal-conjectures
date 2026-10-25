/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor279Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor279Cell078
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (750061/134217728)
  b := (900073/134217728)
  s := [(4395116580729/4398046511104),(-1170875577/4398046511104),(-58240335/2199023255552)]
  L := [(1026189470712860886876789/2475880078570760549798248448),(1492555252549/9007199254740992),(223436333929/13510798882111488),(-464637/70368744177664),(-276091/844424930131968)]
  c := (1866627773257/4503599627370496)
  R := (-389424940004393/100000000000000)
  total := (-4247807338767/1000000000000000)
  k := 12
  n := 32
  sFloor := (2196914612241/4398046511104)
  nFloor := (1602729946171/2251799813685248)
  eFloor := (644235390671/1125899906842624)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=750061,width:=150012,den:=134217728,localDen:=7427640235712281649394745344,lowerC:=3078568412138541466779648,s:=[7422692023207879837791289344,-1977433054602905436291072,-196718363252949642117120],L:=[3078568412138582660630367,1230811391456827322400768,122835423611288343805952,-49043883282715901952,-2428522118594428928],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor279Source.source.poly i) 750061 150012 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor279Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 0 6 WideAnchor279Source.data
    WideAnchor279Source.path_checked WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 6 0 WideAnchor279Source.data
    WideAnchor279Source.path_swapped WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor279Cell078
