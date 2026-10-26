/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor515Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor515Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (869545/8589934592)
  b := (521727/4294967296)
  s := [(4398045342453/4398046511104),(-233731/2199023255552),(-5843/549755813888)]
  L := [(1654901610053/9223372036854775808),(992940772139/13835058055282163712),(198587999317/27670116110564327424),(-1939/1729382256910270464),(-97/1729382256910270464)]
  c := (1654901610053/9223372036854775808)
  R := (-776675485120263/100000000000000)
  total := (-155345496567/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022414123/4398046511104)
  nFloor := (737436041711/2305843009213693952)
  eFloor := (1092111124745/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=869545,width:=173909,den:=8589934592,localDen:=27670116110564327424,lowerC:=4964704830159,s:=[27670108758047981568,-2941016604672,-294087819264],L:=[4964704830159,1985881544278,198587999317,-31024,-1552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor515Source.source.poly i) 869545 173909 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor515Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_checked WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_swapped WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor515Cell056
