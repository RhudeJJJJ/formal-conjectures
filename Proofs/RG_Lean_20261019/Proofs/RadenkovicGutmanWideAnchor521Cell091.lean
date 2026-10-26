/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor521Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor521Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (501569/8388608)
  b := (1203765/16777216)
  s := [(246930875481/274877906944),(-156060358681/4398046511104),(-2900693823/2199023255552)]
  L := [(312114114768633318869/4722366482869645213696),(862384015961/35184372088832),(46136160649/26388279066624),(-257456511/2199023255552),(249581/1649267441664)]
  c := (72669730235/1099511627776)
  R := (-135834822651093/100000000000000)
  total := (-15213362916769/1000000000000000)
  k := 4
  n := 32
  sFloor := (473629032671/1099511627776)
  nFloor := (1174812388507/8796093022208)
  eFloor := (119000586037/1099511627776)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1003138,width:=200627,den:=16777216,localDen:=14167099448608935641088,lowerC:=936342344305402183680,s:=[12726720414762519232512,-502705602552693522432,-18687577658241318912],L:=[936342344305899956607,347241669857403469824,24769162643807141888,-1658650942330896384,2143884465405952],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor521Source.source.poly i) 1003138 200627 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor521Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 6 WideAnchor521Source.data
    WideAnchor521Source.path_checked WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 4 WideAnchor521Source.data
    WideAnchor521Source.path_swapped WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor521Cell091
