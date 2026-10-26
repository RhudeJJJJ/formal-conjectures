/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor039Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor039Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (435483/137438953472)
  b := (1045159/274877906944)
  s := [(1099511626289/1099511627776),(-2379/4398046511104),(-119/2199023255552)]
  L := [(66912148511182113201294501/166153499473114484112975882535043072),(2282106550283/14167099448608935641088),(38035065459/2361183241434822606848),(5/442721857769029238784),(-1/147573952589676412928)]
  c := (475439410587/1180591620717411303424)
  R := (-540819933772831/50000000000000)
  total := (-1359013123/200000000000000)
  k := 32
  n := 32
  sFloor := (2199023251269/4398046511104)
  nFloor := (873487012073/2361183241434822606848)
  eFloor := (1466606419183/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=870966,width:=174193,den:=274877906944,localDen:=498460498419343452338927647605129216,lowerC:=200736445533455761023172608,s:=[498460497745216192176320054059597824,-269628236705925263121186816,-26974157350151413460631552],L:=[200736445533546339603883503,80294486011517866350739456,8029439373195226097123328,5629499534213120,-3377699720527872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor039Source.source.poly i) 870966 174193 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor039Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 18) (CoreQuotient.fused G u 10 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 18 WideAnchor039Source.data
    WideAnchor039Source.path_checked WideAnchor039Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor039Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 10) (CoreQuotient.fused G u 18 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 10 WideAnchor039Source.data
    WideAnchor039Source.path_swapped WideAnchor039Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor039Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor039Cell037
