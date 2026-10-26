/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor535Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor535Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1045159/274877906944)
  b := (627095/137438953472)
  s := [(2199020133291/2199023255552),(-2497795/4398046511104),(-124887/2199023255552)]
  L := [(524730193923/576460752303423488),(209890972149/576460752303423488),(31483344059/864691128455135232),(-1511/36028797018963968),(-113/54043195528445952)]
  c := (524730193923/576460752303423488)
  R := (-86934585012101/12500000000000)
  total := (-5217476323/1000000000000000)
  k := 21
  n := 32
  sFloor := (1099509379753/2199023255552)
  nFloor := (928679706309/1180591620717411303424)
  eFloor := (724284667317/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1045159,width:=209031,den:=274877906944,localDen:=1729382256910270464,lowerC:=1574190581769,s:=[1729379801464307712,-982172958720,-98215133184],L:=[1574190581769,629672916447,62966688118,-72528,-3616],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor535Source.source.poly i) 1045159 209031 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor535Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 13) (CoreQuotient.fused G u 5 13) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 13 WideAnchor535Source.data
    WideAnchor535Source.path_checked WideAnchor535Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor535Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 13 5) (CoreQuotient.fused G u 13 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 13 5 WideAnchor535Source.data
    WideAnchor535Source.path_swapped WideAnchor535Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor535Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor535Cell038
