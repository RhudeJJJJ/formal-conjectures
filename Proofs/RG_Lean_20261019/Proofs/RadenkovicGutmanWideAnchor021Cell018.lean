/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor021Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor021Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (872389/8796093022208)
  b := (523433/4398046511104)
  s := [(2199023255115/2199023255552),(-87/1099511627776),(-9/1099511627776)]
  L := [(4533169204926605777351029187/42535295865117307932921825928971026432),(4831493518765/113336795588871485128704),(241573568075/56668397794435742564352),(-7/7083549724304467820544),(1/3541774862152233910272)]
  c := (503282882583/4722366482869645213696)
  R := (-229621787605313/20000000000000)
  total := (-225876641/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023254923/4398046511104)
  nFloor := (1089398542039/1208925819614629174706176)
  eFloor := (1015011088457/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=872389,width:=174477,den:=8796093022208,localDen:=127605887595351923798765477786913079296,lowerC:=13599507614776487348438827008,s:=[127605887569993495806529016218276331520,-10096948445421382867145981952,-1044511908147039606946136064],L:=[13599507614779817332053087561,5439778102688255130845839360,543975315582565574351257600,-126100789566373888,36028797018963968],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor021Source.source.poly i) 872389 174477 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor021Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 30) (CoreQuotient.fused G u 9 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 30 WideAnchor021Source.data
    WideAnchor021Source.path_checked WideAnchor021Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor021Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 9) (CoreQuotient.fused G u 30 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 9 WideAnchor021Source.data
    WideAnchor021Source.path_swapped WideAnchor021Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor021Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor021Cell018
