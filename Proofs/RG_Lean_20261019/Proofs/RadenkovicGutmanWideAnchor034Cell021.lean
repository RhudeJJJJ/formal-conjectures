/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor034Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor034Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (753743/4398046511104)
  b := (904491/4398046511104)
  s := [(549755813781/549755813888),(-343/4398046511104),(-17/2199023255552)]
  L := [(136234894879153793403405287/1329227995784915872903807060280344576),(4646415821341/113336795588871485128704),(77439955381/18889465931478580854784),(5/7083549724304467820544),(-1/1180591620717411303424)]
  c := (484003574567/4722366482869645213696)
  R := (-230012388712113/20000000000000)
  total := (-390983917/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023254935/4398046511104)
  nFloor := (251725786411/151115727451828646838272)
  eFloor := (955639870707/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=753743,width:=150748,den:=4398046511104,localDen:=3987683987354747618711421180841033728,lowerC:=408704684637361739038457856,s:=[3987683986578617242518829250679668736,-310996167095863355193163776,-30827608400173043955007488],L:=[408704684637461380210215861,163481223137497693093363712,16348057228005911090429952,2814749767106560,-3377699720527872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor034Source.source.poly i) 753743 150748 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor034Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 13) (CoreQuotient.fused G u 10 13) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 13 WideAnchor034Source.data
    WideAnchor034Source.path_checked WideAnchor034Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor034Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 13 10) (CoreQuotient.fused G u 13 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 13 10 WideAnchor034Source.data
    WideAnchor034Source.path_swapped WideAnchor034Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor034Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor034Cell021
