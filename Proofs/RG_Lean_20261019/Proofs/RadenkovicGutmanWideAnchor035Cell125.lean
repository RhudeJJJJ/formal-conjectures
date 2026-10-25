/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor035Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor035Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(2813490889795/144115188075855872),(-402208931383/36028797018963968),(212928021769/72057594037927936)]
  L := [(1183259989092497711061/1180591620717411303424),(-5885945809/6597069766656),(36006871/137438953472),(-3281671/51539607552),(338235/34359738368)]
  c := (1101244618019/1099511627776)
  R := (78745231531/100000000000000)
  total := (693704849501/125000000000000)
  k := 0
  n := 32
  sFloor := (1630511207801/288230376151711744)
  nFloor := 38171667057937122134703252738028350912756940818465790202615930307662699448602984448
  eFloor := 38084098822899497244934223964635429548348093141714473315350423716826674127253274624
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=3541774862152233910272,lowerC:=3547357214465712979968,s:=[69144352107601920,-39538746790674432,10465838125989888],L:=[3549779967277493133183,-3159993094460407808,927890000257744896,-225514713939705856,34864998320701440],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor035Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor035Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 14) (CoreQuotient.fused G u 10 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 14 WideAnchor035Source.data
    WideAnchor035Source.path_checked WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 10) (CoreQuotient.fused G u 14 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 10 WideAnchor035Source.data
    WideAnchor035Source.path_swapped WideAnchor035Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor035Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor035Cell125
