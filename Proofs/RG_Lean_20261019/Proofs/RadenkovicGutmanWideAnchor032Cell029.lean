/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor032Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor032Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1620475/2199023255552)
  b := (972285/1099511627776)
  s := [(4398046489881/4398046511104),(-4243/2199023255552),(-213/1099511627776)]
  L := [(5987137328733/2361183241434822606848),(7184564755037/7083549724304467820544),(119742743293/1180591620717411303424),(-203/442721857769029238784),(-1/73786976294838206464)]
  c := (1496784332183/590295810358705651712)
  R := (-989640765716341/100000000000000)
  total := (-1444731433/1000000000000000)
  k := 29
  n := 32
  sFloor := (2199023240271/4398046511104)
  nFloor := (1075042537489/37778931862957161709568)
  eFloor := (127864227221/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1620475,width:=324095,den:=2199023255552,localDen:=7083549724304467820544,lowerC:=17961411986196,s:=[7083549690122433724416,-13667659677696,-1372242051072],L:=[17961411986199,7184564755037,718456459758,-3248,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor032Source.source.poly i) 1620475 324095 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor032Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 11) (CoreQuotient.fused G u 10 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 11 WideAnchor032Source.data
    WideAnchor032Source.path_checked WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 10) (CoreQuotient.fused G u 11 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 10 WideAnchor032Source.data
    WideAnchor032Source.path_swapped WideAnchor032Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor032Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor032Cell029
