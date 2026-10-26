/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor519Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor519Cell041
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (112877/17179869184)
  b := (1083619/137438953472)
  s := [(68719476665/68719476736),(-1817/4398046511104),(-91/2199023255552)]
  L := [(3048304370789/9444732965739290427392),(457245149407/3541774862152233910272),(91448928749/7083549724304467820544),(-1/885443715538058477568),(1/442721857769029238784)]
  c := (762076092697/2361183241434822606848)
  R := (-1092706878646313/100000000000000)
  total := (-7117825801/500000000000000)
  k := 32
  n := 32
  sFloor := (274877906535/549755813888)
  nFloor := (1378735674129/2361183241434822606848)
  eFloor := (551631318685/590295810358705651712)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=903016,width:=180603,den:=137438953472,localDen:=28334198897217871282176,lowerC:=9144913112364,s:=[28334198867943374192640,-11705933365248,-1172526071808],L:=[9144913112367,3657961195256,365795714996,-32,64],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor519Source.source.poly i) 903016 180603 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor519Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_checked WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_swapped WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor519Cell041
