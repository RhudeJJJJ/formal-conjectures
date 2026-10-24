/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor015Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor015Cell254
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (995973/8192)
  b := 128
  s := [(1282735344151/4611686018427387904),(-202367192549/4611686018427387904),(4717463021/1152921504606846976)]
  L := [(19345418889213980268180775/19342813113834066795298816),(-23415041/1649267441664),(231275/206158430208),(-8059/103079215104),(229/51539607552)]
  c := (1099645291319/1099511627776)
  R := (6077944779/100000000000000)
  total := (82169008629/200000000000000)
  k := 0
  n := 32
  sFloor := (549619001843/4611686018427387904)
  nFloor := 38253156140350860661131796539418692716400520282658938431819849664030785535856522314327116910151038931307924001150133798202759394670329960648416714519740416
  eFloor := 38247982266808458049729943456445877436908155121865123259521227563795988809985351115847538933682790667151552320871693438733540849638419669248700538853261312
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=995973,width:=52603,den:=8192,localDen:=58028439341502200385896448,lowerC:=58035493643249635779674112,s:=[16140545954741747712,-2546368575531122688,237437688225988608],L:=[58036256667641940804542325,-823843515019256922112,65098125238756966400,-4536813674622353408,257831078666960896],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor015Source.source.poly i) 995973 52603 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor015Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 24) (CoreQuotient.fused G u 9 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 24 SymbolicAnchor015Source.data
    SymbolicAnchor015Source.path_checked SymbolicAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor015Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 9) (CoreQuotient.fused G u 24 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 9 SymbolicAnchor015Source.data
    SymbolicAnchor015Source.path_swapped SymbolicAnchor015Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor015Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor015Cell254
