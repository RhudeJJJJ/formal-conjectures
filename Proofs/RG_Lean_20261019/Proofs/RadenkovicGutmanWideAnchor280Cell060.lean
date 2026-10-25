/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor280Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor280Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (901543/4294967296)
  b := (1081851/4294967296)
  s := [(2199020917147/2199023255552),(-1870713/4398046511104),(-93535/2199023255552)]
  L := [(1392482627720289539463469783/2596148429267413814265248164610048),(123676795377/576460752303423488),(12367600359/576460752303423488),(-1899/144115188075855872),(-3/4503599627370496)]
  c := (309193254937/576460752303423488)
  R := (-360961282854461/50000000000000)
  total := (-299136967973/1000000000000000)
  k := 21
  n := 32
  sFloor := (2199019888255/4398046511104)
  nFloor := (914038507689/1152921504606846976)
  eFloor := (906075317307/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=901543,width:=180308,den:=4294967296,localDen:=2596148429267413814265248164610048,lowerC:=1392482627719743972680138752,s:=[2596145668566064970567069181411328,-1104274046283565325831110656,-110426637243803066265763840],L:=[1392482627720289539463469783,556990769574234282358996992,55698720368259612555608064,-34209342769506287616,-1729382256910270464],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor280Source.source.poly i) 901543 180308 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor280Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 0 6 WideAnchor280Source.data
    WideAnchor280Source.path_checked WideAnchor280Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor280Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 0 WideAnchor280Source.data
    WideAnchor280Source.path_swapped WideAnchor280Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor280Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor280Cell060
