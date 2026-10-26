/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor524Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor524Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302419/137438953472)
  b := (1451611/549755813888)
  s := [(1099511627599/1099511627776),(-285/4398046511104),(-13/2199023255552)]
  L := [(342703418127/9444732965739290427392),(1096650031569/75557863725914323419136),(164497368799/113336795588871485128704),(1/2361183241434822606848),(-1/7083549724304467820544)]
  c := (342703418127/9444732965739290427392)
  R := (-150247580881189/12500000000000)
  total := (-2624196653/500000000000000)
  k := 35
  n := 32
  sFloor := (1099511627521/2199023255552)
  nFloor := (1048828349367/18889465931478580854784)
  eFloor := (581330073255/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1209676,width:=241935,den:=549755813888,localDen:=226673591177742970257408,lowerC:=8224882035048,s:=[226673591141252928110592,-14688788152320,-1340029796352],L:=[8224882035048,3289950094707,328994737598,96,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor524Source.source.poly i) 1209676 241935 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor524Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 6 WideAnchor524Source.data
    WideAnchor524Source.path_checked WideAnchor524Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor524Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 6 4 WideAnchor524Source.data
    WideAnchor524Source.path_swapped WideAnchor524Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor524Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor524Cell035
