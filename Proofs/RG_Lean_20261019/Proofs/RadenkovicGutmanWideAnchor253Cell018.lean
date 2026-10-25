/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor253Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor253Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (872389/8796093022208)
  b := (523433/4398046511104)
  s := [(2199023255545/2199023255552),(-3/2199023255552)]
  L := [(462095150297/302231454903657293676544),(2218046551367/3626777458843887524118528),(110901819095/1813388729421943762059264),(-5/226673591177742970257408),(1/113336795588871485128704)]
  c := (462095150297/302231454903657293676544)
  R := (-68016108559573/5000000000000)
  total := (-267970703/1000000000000000)
  k := 40
  n := 32
  sFloor := (1099511627771/2199023255552)
  nFloor := (5941458897/9444732965739290427392)
  eFloor := (1564207533275/2417851639229258349412352)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=872389,width:=174477,den:=8796093022208,localDen:=3626777458843887524118528,lowerC:=5545141803564,s:=[3626777458832342652026880,-4947802324992],L:=[5545141803564,2218046551367,221803638190,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor253Source.source.poly i) 872389 174477 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor253Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 30) (CoreQuotient.fused G u 0 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 30 WideAnchor253Source.data
    WideAnchor253Source.path_checked WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 0) (CoreQuotient.fused G u 30 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 0 WideAnchor253Source.data
    WideAnchor253Source.path_swapped WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor253Cell018
