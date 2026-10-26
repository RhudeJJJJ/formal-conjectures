/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor426Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor426Cell024
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (651233/2199023255552)
  b := (1562959/4398046511104)
  s := [(4398046511093/4398046511104),(-3/4398046511104),(-1/2199023255552)]
  L := [(2034894099047/2417851639229258349412352),(2441871044041/7253554917687775048237056),(122093458481/3626777458843887524118528),(-1/113336795588871485128704),(1/226673591177742970257408)]
  c := (2034894099047/2417851639229258349412352)
  R := (-1390172836583347/100000000000000)
  total := (-408918629/500000000000000)
  k := 41
  n := 32
  sFloor := (274877906943/549755813888)
  nFloor := (798422726729/604462909807314587353088)
  eFloor := (573800362839/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1302466,width:=260493,den:=4398046511104,localDen:=7253554917687775048237056,lowerC:=6104682297141,s:=[7253554917669633106378752,-4947802324992,-3298534883328],L:=[6104682297141,2441871044041,244186916962,-64,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor426Source.source.poly i) 1302466 260493 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor426Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 6 WideAnchor426Source.data
    WideAnchor426Source.path_checked WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 6 2 WideAnchor426Source.data
    WideAnchor426Source.path_swapped WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor426Cell024
