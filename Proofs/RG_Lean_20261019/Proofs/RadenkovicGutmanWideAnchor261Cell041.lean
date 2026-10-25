/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor261Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor261Cell041
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (112877/17179869184)
  b := (1083619/137438953472)
  s := [(1099511590659/1099511627776),(-29693/2199023255552),(-1485/1099511627776)]
  L := [(2606428880301540853886302009/166153499473114484112975882535043072),(5555930789221/885443715538058477568),(277796155871/442721857769029238784),(-1897/55340232221128654848),(-47/27670116110564327424)]
  c := (1157486941983/73786976294838206464)
  R := (-898522078766871/100000000000000)
  total := (-11683947271/1000000000000000)
  k := 26
  n := 32
  sFloor := (2199023148655/4398046511104)
  nFloor := (964305917261/295147905179352825856)
  eFloor := (518788989179/147573952589676412928)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=903016,width:=180603,den:=137438953472,localDen:=498460498419343452338927647605129216,lowerC:=7819286640901280583596900352,s:=[498460481592456084850355993516703744,-6730618942840722015853215744,-673220565797896621664501760],L:=[7819286640904622561658906027,3127710979003995169281277952,312770666016397956170645504,-17086656986243661824,-846676729945653248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor261Source.source.poly i) 903016 180603 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor261Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 38) (CoreQuotient.fused G u 0 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 38 WideAnchor261Source.data
    WideAnchor261Source.path_checked WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 0) (CoreQuotient.fused G u 38 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 0 WideAnchor261Source.data
    WideAnchor261Source.path_swapped WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor261Cell041
