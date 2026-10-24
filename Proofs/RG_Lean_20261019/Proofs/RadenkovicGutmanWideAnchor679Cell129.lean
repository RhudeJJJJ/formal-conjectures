/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor679Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor679Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(2533455400793/1152921504606846976),(-1451810556717/1152921504606846976),(96245229059/288230376151711744)]
  L := [(9449758066362109653871/9444732965739290427392),(-930913899/4398046511104),(137877353/2199023255552),(-4224999/274877906944),(328691/137438953472)]
  c := (1099918566215/1099511627776)
  R := (370039881/2000000000000)
  total := (2707499026573/1000000000000000)
  k := 0
  n := 32
  sFloor := (183328220039/288230376151711744)
  nFloor := 532842276373484032583905349182329943877402821685726931271443902627840000
  eFloor := 532556585024416502524562430996441156891341305093155175677831780040179712
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=9444732965739290427392,lowerC:=9448228540313271009280,s:=[20754066643296256,-11893232080625664,3153763665805312],L:=[9449758066362109653871,-1999122375798423552,592178721994047488,-145169860245061632,22587473527832576],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor679Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor679Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 8) (CoreQuotient.fused G u 8 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 8 WideAnchor679Source.data
    WideAnchor679Source.path_checked WideAnchor679Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor679Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 8) (CoreQuotient.fused G u 8 8) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 8 8 WideAnchor679Source.data
    WideAnchor679Source.path_swapped WideAnchor679Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor679Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor679Cell129
