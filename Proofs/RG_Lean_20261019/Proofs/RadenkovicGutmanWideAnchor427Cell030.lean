/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor427Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor427Cell030
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (972285/1099511627776)
  b := (583371/549755813888)
  s := [(4398046511005/4398046511104),(-37/4398046511104),(-3/2199023255552)]
  L := [(4295971100577/604462909807314587353088),(1718388440239/604462909807314587353088),(257758265921/906694364710971881029632),(7/37778931862957161709568),(-5/56668397794435742564352)]
  c := (134249096893/18889465931478580854784)
  R := (-64174821295443/5000000000000)
  total := (-2253383821/1000000000000000)
  k := 38
  n := 32
  sFloor := (2199023255481/4398046511104)
  nFloor := (1624101442539/151115727451828646838272)
  eFloor := (1273892960061/75557863725914323419136)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=972285,width:=194457,den:=1099511627776,localDen:=1813388729421943762059264,lowerC:=12887913301728,s:=[1813388729381124392878080,-15255723835392,-2473901162496],L:=[12887913301731,5155165320717,515516531842,336,-160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor427Source.source.poly i) 972285 194457 1099511627776
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor427Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 2 6 WideAnchor427Source.data
    WideAnchor427Source.path_checked WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 2 WideAnchor427Source.data
    WideAnchor427Source.path_swapped WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor427Cell030
