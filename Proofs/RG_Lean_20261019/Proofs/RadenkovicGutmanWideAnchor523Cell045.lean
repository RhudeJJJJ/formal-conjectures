/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor523Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor523Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (468123/34359738368)
  b := (1123495/68719476736)
  s := [(4398046485043/4398046511104),(-10425/4398046511104),(-521/2199023255552)]
  L := [(3907245618939/2361183241434822606848),(2344344872491/3541774862152233910272),(39072373163/590295810358705651712),(17/221360928884514619392),(1/36893488147419103232)]
  c := (1953622809469/1180591620717411303424)
  R := (-1010979801167643/100000000000000)
  total := (-27292091923/1000000000000000)
  k := 30
  n := 32
  sFloor := (549755809197/1099511627776)
  nFloor := (1565273612963/590295810358705651712)
  eFloor := (1401262299267/295147905179352825856)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=936246,width:=187249,den:=68719476736,localDen:=7083549724304467820544,lowerC:=11721736856814,s:=[7083549682330289307648,-16790637772800,-1678258470912],L:=[11721736856817,4688689744982,468868477956,544,192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor523Source.source.poly i) 936246 187249 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor523Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 6 WideAnchor523Source.data
    WideAnchor523Source.path_checked WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 6 4 WideAnchor523Source.data
    WideAnchor523Source.path_swapped WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor523Cell045
