/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor041Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor041Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1451611/549755813888)
  b := (435483/137438953472)
  s := [(2199023253137/2199023255552),(-483/1099511627776),(-3/68719476736)]
  L := [(5866178377365/18889465931478580854784),(7039384954961/56668397794435742564352),(351967792757/28334198897217871282176),(-35/3541774862152233910272),(7/1770887431076116955136)]
  c := (1466544594341/4722366482869645213696)
  R := (-1094633343336323/100000000000000)
  total := (-5731159167/1000000000000000)
  k := 32
  n := 32
  sFloor := (2199023252075/4398046511104)
  nFloor := (612448778189/2361183241434822606848)
  eFloor := (1082715917691/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1451611,width:=290321,den:=549755813888,localDen:=56668397794435742564352,lowerC:=17598535132092,s:=[56668397732201666445312,-24893630447616,-2473901162496],L:=[17598535132095,7039384954961,703935585514,-560,224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor041Source.source.poly i) 1451611 290321 549755813888
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor041Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 20) (CoreQuotient.fused G u 10 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 20 WideAnchor041Source.data
    WideAnchor041Source.path_checked WideAnchor041Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor041Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 10) (CoreQuotient.fused G u 20 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 10 WideAnchor041Source.data
    WideAnchor041Source.path_swapped WideAnchor041Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor041Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor041Cell036
