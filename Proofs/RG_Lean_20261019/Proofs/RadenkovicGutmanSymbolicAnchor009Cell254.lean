/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor009Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor009Cell254
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (995973/8192)
  b := 128
  s := [(1282735344151/4611686018427387904),(-202367192549/4611686018427387904),(4717463021/1152921504606846976)]
  L := [(4836354722303451036060721/4835703278458516698824704),(-23415041/1649267441664),(231275/206158430208),(-8059/103079215104),(229/51539607552)]
  c := (1099645291319/1099511627776)
  R := (6077944779/100000000000000)
  total := (102711260779/250000000000000)
  k := 0
  n := 32
  sFloor := (549619001843/4611686018427387904)
  nFloor := 3664569942900264086662832030707749908469518200059804251437497541083953656732363634939481541451301619315296372012715954135850024960
  eFloor := 3664074296962006302331831223282966628078732508053364120919510690277678180496343712210686148949743023436955692388877357794614837248
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=995973,width:=52603,den:=8192,localDen:=14507109835375550096474112,lowerC:=14508873410812408944918528,s:=[4035136488685436928,-636592143882780672,59359422056497152],L:=[14509064166910353108182163,-205960878754814230528,16274531309689241600,-1134203418655588352,64457769666740224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor009Source.source.poly i) 995973 52603 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor009Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 18) (CoreQuotient.fused G u 9 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 18 SymbolicAnchor009Source.data
    SymbolicAnchor009Source.path_checked SymbolicAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor009Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 9) (CoreQuotient.fused G u 18 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 9 SymbolicAnchor009Source.data
    SymbolicAnchor009Source.path_swapped SymbolicAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor009Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor009Cell254
