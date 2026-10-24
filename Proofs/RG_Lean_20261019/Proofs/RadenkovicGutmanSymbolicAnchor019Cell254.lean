/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor019Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor019Cell254
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (995973/8192)
  b := 128
  s := [(1282735344151/4611686018427387904),(-202367192549/4611686018427387904),(4717463021/1152921504606846976)]
  L := [(9672709444607035021092187/9671406556917033397649408),(-23415041/1649267441664),(231275/206158430208),(-8059/103079215104),(229/51539607552)]
  c := (1099645291319/1099511627776)
  R := (6077944779/100000000000000)
  total := (10271126079/25000000000000)
  k := 0
  n := 32
  sFloor := (549619001843/4611686018427387904)
  nFloor := 1827104743649166771973604845729008867174330961273685245407857558316938759420532178939174702719236375327650513555498603640479564743778822510337190461774362818989845368537088
  eFloor := 1826857621323959808397556361896846986508106035261897356710026425291867971689168025711990491064878835068848945301924207251735655077198673747531049871467931898364123873804288
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=995973,width:=52603,den:=8192,localDen:=29014219670751100192948224,lowerC:=29017746821624817889837056,s:=[8070272977370873856,-1273184287765561344,118718844112994304],L:=[29018128333821105063276561,-411921757509628461056,32549062619378483200,-2268406837311176704,128915539333480448],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor019Source.source.poly i) 995973 52603 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor019Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 28) (CoreQuotient.fused G u 9 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 28 SymbolicAnchor019Source.data
    SymbolicAnchor019Source.path_checked SymbolicAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor019Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 9) (CoreQuotient.fused G u 28 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 9 SymbolicAnchor019Source.data
    SymbolicAnchor019Source.path_swapped SymbolicAnchor019Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor019Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor019Cell254
