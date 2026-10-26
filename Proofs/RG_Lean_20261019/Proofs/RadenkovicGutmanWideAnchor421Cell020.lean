/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor421Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor421Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1256239/8796093022208)
  b := (753743/4398046511104)
  s := [(2199023255551/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(113631689616071621995662001/680564733841876926926749214863536422912),(1937757948577/29014219670751100192948224),(12110948611/1813388729421943762059264),(1/226673591177742970257408),(-1/453347182355485940514816)]
  c := (100925214511/604462909807314587353088)
  R := (-1471049081755147/100000000000000)
  total := (-52188181/125000000000000)
  k := 43
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1577946706083/4835703278458516698824704)
  eFloor := (884169461237/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1256239,width:=251247,den:=8796093022208,localDen:=2041694201525630780780247644590609268736,lowerC:=340895068848020231754350592,s:=[2041694201524702325750783609384434925568,464227514732017603087171584,-928455029464035206174343168],L:=[340895068848214865986986003,136357593361649905463984128,13635715912900706528395264,9007199254740992,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor421Source.source.poly i) 1256239 251247 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor421Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 4 WideAnchor421Source.data
    WideAnchor421Source.path_checked WideAnchor421Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor421Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 2 WideAnchor421Source.data
    WideAnchor421Source.path_swapped WideAnchor421Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor421Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor421Cell020
