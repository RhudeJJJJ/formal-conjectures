/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor012Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor012Cell254
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (995973/8192)
  b := 128
  s := [(1282735344151/4611686018427387904),(-202367192549/4611686018427387904),(4717463021/1152921504606846976)]
  L := [(9672709444606949565529777/9671406556917033397649408),(-23415041/1649267441664),(231275/206158430208),(-8059/103079215104),(229/51539607552)]
  c := (1099645291319/1099511627776)
  R := (6077944779/100000000000000)
  total := (410845043131/1000000000000000)
  k := 0
  n := 32
  sFloor := (549619001843/4611686018427387904)
  nFloor := 11839821206973626942159356162921213220236241904470281648293504004177850295461365229427141141004021956242445183856035211108754294620701845356544
  eFloor := 11838219829621152809323869702509807387093526924207070960152543752045186124134782847296776966817019316459913018718416496817682567423059367559168
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=995973,width:=52603,den:=8192,localDen:=29014219670751100192948224,lowerC:=29017746821624817889837056,s:=[8070272977370873856,-1273184287765561344,118718844112994304],L:=[29018128333820848696589331,-411921757509628461056,32549062619378483200,-2268406837311176704,128915539333480448],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor012Source.source.poly i) 995973 52603 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor012Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 21) (CoreQuotient.fused G u 9 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 21 SymbolicAnchor012Source.data
    SymbolicAnchor012Source.path_checked SymbolicAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor012Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 9) (CoreQuotient.fused G u 21 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 9 SymbolicAnchor012Source.data
    SymbolicAnchor012Source.path_swapped SymbolicAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor012Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor012Cell254
