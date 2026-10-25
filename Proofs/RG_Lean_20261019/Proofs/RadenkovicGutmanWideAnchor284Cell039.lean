/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor284Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor284Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (627095/137438953472)
  b := (376257/68719476736)
  s := [(2199023253347/2199023255552),(-1767/4398046511104),(-87/2199023255552)]
  L := [(1898529133591/4722366482869645213696),(189852913149/1180591620717411303424),(113911747415/7083549724304467820544),(-3/147573952589676412928),(1/442721857769029238784)]
  c := (1898529133591/4722366482869645213696)
  R := (-1081724821911583/100000000000000)
  total := (-244641819/25000000000000)
  k := 32
  n := 32
  sFloor := (274877906547/549755813888)
  nFloor := (1692901880815/4722366482869645213696)
  eFloor := (1055580714187/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=627095,width:=125419,den:=137438953472,localDen:=14167099448608935641088,lowerC:=5695587400773,s:=[14167099434403331309568,-5691905409024,-560493232128],L:=[5695587400773,2278234957788,227823494830,-288,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor284Source.source.poly i) 627095 125419 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor284Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 8 WideAnchor284Source.data
    WideAnchor284Source.path_checked WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 8 0 WideAnchor284Source.data
    WideAnchor284Source.path_swapped WideAnchor284Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor284Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor284Cell039
