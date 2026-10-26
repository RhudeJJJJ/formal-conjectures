/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor526Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor526Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (669709/32768)
  b := (1607301/65536)
  s := [(4177255022969/72057594037927936),(-1190366891009/36028797018963968),(314211700755/36028797018963968)]
  L := [(1186051408184215094977/1180591620717411303424),(-11926258975/6597069766656),(432666011/824633720832),(-6493315/51539607552),(1989017/103079215104)]
  c := (1103068321409/1099511627776)
  R := (161478666221/100000000000000)
  total := (1577977111977/200000000000000)
  k := 0
  n := 32
  sFloor := (606236160615/36028797018963968)
  nFloor := 10524801629972794171453976647858913280
  eFloor := 10475137723279905575128170564702699520
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1339418,width:=267883,den:=65536,localDen:=3541774862152233910272,lowerC:=3553231774278953730048,s:=[205320438888972288,-117017826853748736,30888267031019520],L:=[3558154224552645284931,-6402861532656435200,1858286367335776256,-446217209082019840,68342103729504256],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor526Source.source.poly i) 1339418 267883 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor526Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 4 6 WideAnchor526Source.data
    WideAnchor526Source.path_checked WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 4 WideAnchor526Source.data
    WideAnchor526Source.path_swapped WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor526Cell123
