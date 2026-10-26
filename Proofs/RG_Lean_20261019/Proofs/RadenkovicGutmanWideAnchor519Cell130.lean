/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor519Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor519Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1199841/16384)
  b := (1439809/16384)
  s := [(5866420506009/4611686018427387904),(-3362456727153/4611686018427387904),(445890718413/2305843009213693952)]
  L := [(18896456884553606755293/18889465931478580854784),(-1944564457/13194139533312),(288317281/6597069766656),(-8843963/824633720832),(688535/412316860416)]
  c := (549897302393/549755813888)
  R := (12866648917/100000000000000)
  total := (1129903487637/500000000000000)
  k := 0
  n := 32
  sFloor := (1697872607841/4611686018427387904)
  nFloor := 1137252142284888425070653985627282837856059392
  eFloor := 1136828509231735192570064390159525587032473600
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1199841,width:=239968,den:=16384,localDen:=56668397794435742564352,lowerC:=56682982318477380943872,s:=[72086575177838592,-41317868263256064,10958210295717888],L:=[56689370653660820265879,-8351840747778998272,2476626585533284352,-607752509632544768,94631529828843520],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor519Source.source.poly i) 1199841 239968 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor519Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_checked WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 4 4 WideAnchor519Source.data
    WideAnchor519Source.path_swapped WideAnchor519Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor519Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor519Cell130
