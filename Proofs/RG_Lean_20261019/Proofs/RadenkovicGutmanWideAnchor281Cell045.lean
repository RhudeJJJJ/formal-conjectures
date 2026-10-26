/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor281Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor281Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (468123/34359738368)
  b := (1123495/68719476736)
  s := [(2199014942313/2199023255552),(-1662637/1099511627776),(-83129/549755813888)]
  L := [(583486729245/288230376151711744),(350090255249/432345564227567616),(35008424795/432345564227567616),(-56341/216172782113783808),(-703/54043195528445952)]
  c := (583486729245/288230376151711744)
  R := (-655512446371503/100000000000000)
  total := (-8803103179/500000000000000)
  k := 19
  n := 32
  sFloor := (2199011284523/4398046511104)
  nFloor := (40315516463/9223372036854775808)
  eFloor := (1204598284699/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=936246,width:=187249,den:=68719476736,localDen:=864691128455135232,lowerC:=1750460187735,s:=[864687859556548608,-1307550941184,-130750611456],L:=[1750460187735,700180510498,70016849590,-225364,-11248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor281Source.source.poly i) 936246 187249 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor281Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 7) (CoreQuotient.fused G u 0 7) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 7 WideAnchor281Source.data
    WideAnchor281Source.path_checked WideAnchor281Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor281Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 7 0) (CoreQuotient.fused G u 7 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 7 0 WideAnchor281Source.data
    WideAnchor281Source.path_swapped WideAnchor281Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor281Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor281Cell045
