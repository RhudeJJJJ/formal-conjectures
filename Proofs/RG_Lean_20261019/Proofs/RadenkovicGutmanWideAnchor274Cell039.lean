/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor274Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor274Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (627095/137438953472)
  b := (376257/68719476736)
  s := [(4398046509801/4398046511104),(-523/4398046511104),(-25/2199023255552)]
  L := [(2143833178233/9444732965739290427392),(428766635555/4722366482869645213696),(21438331759/2361183241434822606848),(-1/590295810358705651712)]
  c := (2143833178233/9444732965739290427392)
  R := (-1110306381671307/100000000000000)
  total := (-2511622969/250000000000000)
  k := 33
  n := 32
  sFloor := (1099511627307/2199023255552)
  nFloor := (277203909425/590295810358705651712)
  eFloor := (1446996626481/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=627095,width:=125419,den:=137438953472,localDen:=9444732965739290427392,lowerC:=2143833178233,s:=[9444732962941119234048,-1123133947904,-107374182400],L:=[2143833178233,857533271110,85753327036,-16],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor274Source.source.poly i) 627095 125419 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor274Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 0 4 WideAnchor274Source.data
    WideAnchor274Source.path_checked WideAnchor274Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor274Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 0 WideAnchor274Source.data
    WideAnchor274Source.path_swapped WideAnchor274Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor274Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor274Cell039
