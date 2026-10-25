/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor498Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor498Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302419/137438953472)
  b := (1451611/549755813888)
  s := [(4398046505095/4398046511104),(-2401/4398046511104),(-121/2199023255552)]
  L := [(4845818034807/9444732965739290427392),(5814976822127/28334198897217871282176),(96916199455/4722366482869645213696),(-83/1770887431076116955136),(1/295147905179352825856)]
  c := (1211454508701/2361183241434822606848)
  R := (-534765174820599/50000000000000)
  total := (-291594359/62500000000000)
  k := 31
  n := 32
  sFloor := (1099511625613/2199023255552)
  nFloor := (299167032559/1180591620717411303424)
  eFloor := (796559955869/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1209676,width:=241935,den:=549755813888,localDen:=28334198897217871282176,lowerC:=14537454104412,s:=[28334198858505183559680,-15468324716544,-1559073128448],L:=[14537454104421,5814976822127,581497196730,-1328,96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor498Source.source.poly i) 1209676 241935 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor498Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 28) (CoreQuotient.fused G u 4 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 28 WideAnchor498Source.data
    WideAnchor498Source.path_checked WideAnchor498Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor498Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 4) (CoreQuotient.fused G u 28 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 4 WideAnchor498Source.data
    WideAnchor498Source.path_swapped WideAnchor498Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor498Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor498Cell035
