/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor018Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor018Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (435483/137438953472)
  b := (1045159/274877906944)
  s := [(4398043935915/4398046511104),(-128759/549755813888),(-3219/137438953472)]
  L := [(7993275837187/18446744073709551616),(3197304737023/18446744073709551616),(159864667963/9223372036854775808),(-9641/1152921504606846976),(-239/576460752303423488)]
  c := (31223733739/72057594037927936)
  R := (-732589888600771/100000000000000)
  total := (-4583099489/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199021401417/4398046511104)
  nFloor := (1359767235437/1180591620717411303424)
  eFloor := (459355415537/590295810358705651712)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=870966,width:=174193,den:=274877906944,localDen:=18446744073709551616,lowerC:=7993275837184,s:=[18446733272584028160,-4320435109888,-432046866432],L:=[7993275837187,3197304737023,319729335926,-154256,-7648],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor018Source.source.poly i) 870966 174193 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor018Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 27) (CoreQuotient.fused G u 9 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 27 WideAnchor018Source.data
    WideAnchor018Source.path_checked WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 9) (CoreQuotient.fused G u 27 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 9 WideAnchor018Source.data
    WideAnchor018Source.path_swapped WideAnchor018Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor018Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor018Cell037
