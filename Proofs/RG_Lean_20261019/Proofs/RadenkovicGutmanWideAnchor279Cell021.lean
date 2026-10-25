/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor279Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor279Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (753743/4398046511104)
  b := (904491/4398046511104)
  s := [(4398046511101/4398046511104),(-3/4398046511104),(1/2199023255552)]
  L := [(530844954366027941443084817/1361129467683753853853498429727072845824),(4526238298589/29014219670751100192948224),(75437004701/4835703278458516698824704),(13/1813388729421943762059264),(-1/302231454903657293676544)]
  c := (942970065349/2417851639229258349412352)
  R := (-1428631062517107/100000000000000)
  total := (-243233311/500000000000000)
  k := 42
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (808699090451/1208925819614629174706176)
  eFloor := (1300450728045/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=753743,width:=150748,den:=4398046511104,localDen:=4083388403051261561560495289181218537472,lowerC:=1592534863097733248307953664,s:=[4083388403048476196472103183562695507968,-2785365088392105618523029504,1856910058928070412348686336],L:=[1592534863098083824329254451,637011409841109006593032192,63700887424006866566381568,29273397577908224,-13510798882111488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor279Source.source.poly i) 753743 150748 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor279Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 0 6 WideAnchor279Source.data
    WideAnchor279Source.path_checked WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 6 0 WideAnchor279Source.data
    WideAnchor279Source.path_swapped WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor279Cell021
