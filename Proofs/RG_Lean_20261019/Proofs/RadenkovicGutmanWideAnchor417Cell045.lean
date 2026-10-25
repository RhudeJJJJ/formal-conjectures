/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor417Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor417Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (468123/34359738368)
  b := (1123495/68719476736)
  s := [(4398046495811/4398046511104),(-6119/4398046511104),(-305/2199023255552)]
  L := [(45857886292993771194943003/20769187434139310514121985316880384),(6256118997625/7083549724304467820544),(104268537729/1180591620717411303424),(-61/442721857769029238784),(-1/73786976294838206464)]
  c := (1303359519311/590295810358705651712)
  R := (-996559458301869/100000000000000)
  total := (-26899161869/1000000000000000)
  k := 29
  n := 32
  sFloor := (2199023244541/4398046511104)
  nFloor := (1296493322467/295147905179352825856)
  eFloor := (1020882346635/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=936246,width:=187249,den:=68719476736,localDen:=62307562302417931542365955950641152,lowerC:=137573658878878321534304256,s:=[62307562085760479674789503191482368,-86688481526038077187817472,-8641930663651450741063680],L:=[137573658878981313584829009,55029404661112169824256000,5502934542923330897313792,-8584986789675008,-844424930131968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor417Source.source.poly i) 936246 187249 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor417Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 2 4 WideAnchor417Source.data
    WideAnchor417Source.path_checked WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 4 2 WideAnchor417Source.data
    WideAnchor417Source.path_swapped WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor417Cell045
