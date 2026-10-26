/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor479Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor479Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (753743/4398046511104)
  b := (904491/4398046511104)
  s := [(549755813887/549755813888),(-5/4398046511104),(1/2199023255552)]
  L := [(39348083929847663847623970935/87112285931760246646623899502532662132736),(436849748809/2417851639229258349412352),(131054403019/7253554917687775048237056),(1/302231454903657293676544),(-1/453347182355485940514816)]
  c := (2184257437689/4835703278458516698824704)
  R := (-710644294116281/50000000000000)
  total := (-241974953/500000000000000)
  k := 42
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (1246168444897/2417851639229258349412352)
  eFloor := (594393165591/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=753743,width:=150748,den:=4398046511104,localDen:=261336857795280739939871698507597986398208,lowerC:=118044251789488977427644284928,s:=[261336857794805370964786112482036722696192,-297105609428491265975789813760,118842243771396506390315925504],L:=[118044251789542991542871912805,47217512782874572290665742336,4721732484813049648111419392,864691128455135232,-576460752303423488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor479Source.source.poly i) 753743 150748 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor479Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 10) (CoreQuotient.fused G u 4 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 4 10 WideAnchor479Source.data
    WideAnchor479Source.path_checked WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 4) (CoreQuotient.fused G u 10 4) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 4 WideAnchor479Source.data
    WideAnchor479Source.path_swapped WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor479Cell021
