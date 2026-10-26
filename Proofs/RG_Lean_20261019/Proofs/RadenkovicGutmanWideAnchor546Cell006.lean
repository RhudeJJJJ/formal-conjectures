/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor546Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor546Cell006
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (195689/17592186044416)
  b := (939307/70368744177664)
  s := [(549755813885/549755813888),(-9/4398046511104),(-1/2199023255552)]
  L := [(1697500537963/604462909807314587353088),(1357998695467/1208925819614629174706176),(203699544073/1813388729421943762059264),(1/75557863725914323419136),(-1/113336795588871485128704)]
  c := (1697500537963/604462909807314587353088)
  R := (-33248061563677/2500000000000)
  total := (-2937857/100000000000000)
  k := 39
  n := 32
  sFloor := (1099511627767/2199023255552)
  nFloor := (654434278559/77371252455336267181195264)
  eFloor := (628903186735/77371252455336267181195264)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=782756,width:=156551,den:=70368744177664,localDen:=3626777458843887524118528,lowerC:=10185003227778,s:=[3626777458824096314818560,-7421703487488,-1649267441664],L:=[10185003227778,4073996086401,407399088146,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor546Source.source.poly i) 782756 156551 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor546Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 24) (CoreQuotient.fused G u 5 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 24 WideAnchor546Source.data
    WideAnchor546Source.path_checked WideAnchor546Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor546Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 5) (CoreQuotient.fused G u 24 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 5 WideAnchor546Source.data
    WideAnchor546Source.path_swapped WideAnchor546Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor546Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor546Cell006
