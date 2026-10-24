/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor006Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell169
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (38645/1048576)
  b := (85019/2097152)
  s := [(688400066011/4398046511104),(-14468996389/35184372088832),(11704711075/17592186044416)]
  L := [(4743553047503369472457/4722366482869645213696),(-4545921535/1099511627776),(-2844718967/1649267441664),(24710551/137438953472),(-631451/51539607552)]
  c := (1098186321863/1099511627776)
  R := (-1507607169/2500000000000)
  total := (1735489559/500000000000000)
  k := 1
  n := 32
  sFloor := (1374991507473/17592186044416)
  nFloor := (1058922801801/8796093022208)
  eFloor := (384422024727/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=77290,width:=7729,den:=2097152,localDen:=14167099448608935641088,lowerC:=14150023011948344377344,s:=[2217491827561114632192,-5825987465315352576,9425878364297625600],L:=[14230659142510108417371,-58573752969021358080,-24435949859151806464,2547144201867362304,-173571929217695744],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor006Source.source.poly i) 77290 7729 2097152
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
end Gebendorfer.RadenkovicGutman.SymbolicAnchor006Cell169
