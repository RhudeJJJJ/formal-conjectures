/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor006Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell237
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1576395/65536)
  b := (867017/32768)
  s := [(2570664141603/72057594037927936),(-378695500601/36028797018963968),(60226774305/36028797018963968)]
  L := [(18952998199040124607435/18889465931478580854784),(-4362211553/6597069766656),(160246133/1649267441664),(-5102449/412316860416),(120433/103079215104)]
  c := (1102577166047/1099511627776)
  R := (69605282491/50000000000000)
  total := (229833121867/62500000000000)
  k := 0
  n := 32
  sFloor := (1933726689011/144115188075855872)
  nFloor := 488976168496439548031694882684795893222053533982201747450972966828219532574720
  eFloor := 487302302852429212030427961633002042371089922354081458961426677863052371558400
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1576395,width:=157639,den:=65536,localDen:=56668397794435742564352,lowerC:=56826394433858719186944,s:=[2021652542209130496,-595636519857291264,94728525140459520],L:=[56858994597120373822305,-37471111916736741376,5506015204363730944,-701275250704252928,66208741933973504],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor006Source.source.poly i) 1576395 157639 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor006Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 15) (CoreQuotient.fused G u 9 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 15 SymbolicAnchor006Source.data
    SymbolicAnchor006Source.path_checked SymbolicAnchor006Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor006Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 9) (CoreQuotient.fused G u 15 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 9 SymbolicAnchor006Source.data
    SymbolicAnchor006Source.path_swapped SymbolicAnchor006Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor006Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell237
