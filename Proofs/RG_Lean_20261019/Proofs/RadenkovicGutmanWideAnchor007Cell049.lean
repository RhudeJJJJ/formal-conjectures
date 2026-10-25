/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor007Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor007Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (970699/34359738368)
  b := (582419/17179869184)
  s := [(1099499632053/1099511627776),(-9596381/2199023255552),(-119943/274877906944)]
  L := [(822044866877/144115188075855872),(3945752242445/1729382256910270464),(197277427571/864691128455135232),(-234287/108086391056891904),(-5855/54043195528445952)]
  c := (822044866877/144115188075855872)
  R := (-603716423941423/100000000000000)
  total := (-16790759621/500000000000000)
  k := 18
  n := 32
  sFloor := (2198988708181/4398046511104)
  nFloor := (1779246374887/36893488147419103232)
  eFloor := (850783968699/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=970699,width:=194139,den:=34359738368,localDen:=1729382256910270464,lowerC:=9864538402524,s:=[1729363389269409792,-7546901102592,-754616107008],L:=[9864538402524,3945752242445,394554855142,-3748592,-187360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor007Source.source.poly i) 970699 194139 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor007Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 16) (CoreQuotient.fused G u 9 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 16 WideAnchor007Source.data
    WideAnchor007Source.path_checked WideAnchor007Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor007Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 9) (CoreQuotient.fused G u 16 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 9 WideAnchor007Source.data
    WideAnchor007Source.path_swapped WideAnchor007Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor007Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor007Cell049
