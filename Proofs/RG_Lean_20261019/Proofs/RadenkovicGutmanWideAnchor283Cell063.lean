/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor283Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor283Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1557865/4294967296)
  b := (934719/2147483648)
  s := [(2199013723949/2199023255552),(-7625227/4398046511104),(-381247/2199023255552)]
  L := [(2631876624173/1152921504606846976),(3158239734839/3458764513820540928),(78954771973/864691128455135232),(-61073/216172782113783808),(-763/54043195528445952)]
  c := (657969156043/288230376151711744)
  R := (-649505629030919/100000000000000)
  total := (-464376014857/1000000000000000)
  k := 19
  n := 32
  sFloor := (274876191261/549755813888)
  nFloor := (877474168031/288230376151711744)
  eFloor := (416529348769/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1557865,width:=311573,den:=4294967296,localDen:=3458764513820540928,lowerC:=7895629872516,s:=[3458749521905319936,-5996722520064,-599649681408],L:=[7895629872519,3158239734839,315819087892,-977168,-48832],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor283Source.source.poly i) 1557865 311573 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor283Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 0 8 WideAnchor283Source.data
    WideAnchor283Source.path_checked WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 8 0 WideAnchor283Source.data
    WideAnchor283Source.path_swapped WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor283Cell063
