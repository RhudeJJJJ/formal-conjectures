/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor432Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor432Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1620475/2199023255552)
  b := (972285/1099511627776)
  s := [(2199023255501/2199023255552),(-5/549755813888),(-1/1099511627776)]
  L := [(4322749921709/604462909807314587353088),(1729099968667/604462909807314587353088),(259364995273/906694364710971881029632),(1/37778931862957161709568),(-1/56668397794435742564352)]
  c := (1080687480427/151115727451828646838272)
  R := (-3207964299077/250000000000)
  total := (-1877361927/1000000000000000)
  k := 38
  n := 32
  sFloor := (2199023255479/4398046511104)
  nFloor := (649922263837/75557863725914323419136)
  eFloor := (523160550733/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1620475,width:=324095,den:=2199023255552,localDen:=1813388729421943762059264,lowerC:=12968249765124,s:=[1813388729379887442296832,-16492674416640,-1649267441664],L:=[12968249765127,5187299906001,518729990546,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor432Source.source.poly i) 1620475 324095 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor432Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 8) (CoreQuotient.fused G u 2 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 2 8 WideAnchor432Source.data
    WideAnchor432Source.path_checked WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 2) (CoreQuotient.fused G u 8 2) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 2 WideAnchor432Source.data
    WideAnchor432Source.path_swapped WideAnchor432Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor432Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor432Cell029
