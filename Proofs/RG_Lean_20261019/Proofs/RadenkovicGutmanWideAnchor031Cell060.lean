/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor031Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor031Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (901543/4294967296)
  b := (1081851/4294967296)
  s := [(4398031824233/4398046511104),(-5874705/4398046511104),(-293727/2199023255552)]
  L := [(6019641778029/4611686018427387904),(7223540143213/13835058055282163712),(120391538259/2305843009213693952),(-29779/864691128455135232),(-247/144115188075855872)]
  c := (1504910444507/1152921504606846976)
  R := (-677453816327441/100000000000000)
  total := (-35058555161/125000000000000)
  k := 20
  n := 32
  sFloor := (2199012681037/4398046511104)
  nFloor := (919573952393/576460752303423488)
  eFloor := (1176294133197/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=901543,width:=180308,den:=4294967296,localDen:=13835058055282163712,lowerC:=18058925334084,s:=[13835011854380826624,-18480224010240,-1847970496512],L:=[18058925334087,7223540143213,722349229554,-476464,-23712],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor031Source.source.poly i) 901543 180308 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor031Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 10) (CoreQuotient.fused G u 10 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 10 WideAnchor031Source.data
    WideAnchor031Source.path_checked WideAnchor031Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor031Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 10) (CoreQuotient.fused G u 10 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 10 WideAnchor031Source.data
    WideAnchor031Source.path_swapped WideAnchor031Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor031Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor031Cell060
