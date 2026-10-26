/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor042Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor042Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1085389/4398046511104)
  b := (651233/2199023255552)
  s := [(4398046510331/4398046511104),(-311/4398046511104),(-15/2199023255552)]
  L := [(3491551632023/37778931862957161709568),(1396615505489/37778931862957161709568),(69830517839/18889465931478580854784),(1/1180591620717411303424),(-1/1180591620717411303424)]
  c := (1745775816011/18889465931478580854784)
  R := (-1155233559747647/100000000000000)
  total := (-565569113/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023254995/4398046511104)
  nFloor := (1348135324383/302231454903657293676544)
  eFloor := (640905770155/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1085389,width:=217077,den:=4398046511104,localDen:=37778931862957161709568,lowerC:=3491551632022,s:=[37778931856317142269952,-2671469658112,-257698037760],L:=[3491551632023,1396615505489,139661035678,32,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor042Source.source.poly i) 1085389 217077 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor042Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 21) (CoreQuotient.fused G u 10 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 21 WideAnchor042Source.data
    WideAnchor042Source.path_checked WideAnchor042Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor042Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 10) (CoreQuotient.fused G u 21 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 10 WideAnchor042Source.data
    WideAnchor042Source.path_swapped WideAnchor042Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor042Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor042Cell023
