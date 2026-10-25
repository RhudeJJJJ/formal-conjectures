/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor246Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor246Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1397805/34359738368)
  b := (838683/17179869184)
  s := [(4398044626863/4398046511104),(-23553/137438953472),(-9421/549755813888)]
  L := [(137339235676058410814985685/649037107316853453566312041152512),(4684095421811/55340232221128654848),(234204051395/27670116110564327424),(-17969/3458764513820540928),(-455/1729382256910270464)]
  c := (1951707924889/9223372036854775808)
  R := (-24013353767493/3125000000000)
  total := (-385993041/6250000000000)
  k := 23
  n := 32
  sFloor := (2199021898899/4398046511104)
  nFloor := (932874143257/9223372036854775808)
  eFloor := (7377929823/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1397805,width:=279561,den:=34359738368,localDen:=1947111321950560360698936123457536,lowerC:=412017707028100518550437888,s:=[1947110487755884356125514207854592,-333677693313086261154545664,-33367060976336195668672512],L:=[412017707028175232444957055,164806956220592702202314752,16480644977987226467041280,-10115647713027555328,-512284457613393920],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor246Source.source.poly i) 1397805 279561 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor246Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 28) (CoreQuotient.fused G u 0 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 28 WideAnchor246Source.data
    WideAnchor246Source.path_checked WideAnchor246Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor246Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 0) (CoreQuotient.fused G u 28 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 0 WideAnchor246Source.data
    WideAnchor246Source.path_swapped WideAnchor246Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor246Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor246Cell051
