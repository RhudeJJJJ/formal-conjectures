/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor393Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor393Cell019
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (523433/4398046511104)
  b := (1256239/8796093022208)
  s := [(4398046511103/4398046511104),(-3/4398046511104),(1/2199023255552)]
  L := [(415119461324523015348558067/2722258935367507707706996859454145691648),(589919671927/9671406556917033397649408),(58991910821/9671406556917033397649408),(1/302231454903657293676544),(-1/604462909807314587353088)]
  c := (1474800588583/9671406556917033397649408)
  R := (-737791802101893/50000000000000)
  total := (-43625173/125000000000000)
  k := 43
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1612977505285/4835703278458516698824704)
  eFloor := (512332516379/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1046866,width:=209373,den:=8796093022208,localDen:=2722258935367507707706996859454145691648,lowerC:=415119461324261686088040448,s:=[2722258935366888737687354169316696129536,-1856910058928070412348686336,1237940039285380274899124224],L:=[415119461324523015348558067,166047625916810153124954112,16604746724458070672408576,9007199254740992,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor393Source.source.poly i) 1046866 209373 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor393Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_checked WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_swapped WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor393Cell019
