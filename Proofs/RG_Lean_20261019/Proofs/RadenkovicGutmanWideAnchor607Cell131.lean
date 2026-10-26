/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor607Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor607Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1439809/16384)
  b := (863885/8192)
  s := [(1697876230219/2305843009213693952),(-973313411207/2305843009213693952),(129085461125/1152921504606846976)]
  L := [(9447163735419639159825/9444732965739290427392),(-21146213/206158430208),(25104499/824633720832),(-1541413/206158430208),(30019/25769803776)]
  c := (549854179707/549755813888)
  R := (178910377/2000000000000)
  total := (188561081363/100000000000000)
  k := 0
  n := 32
  sFloor := (491366870631/2305843009213693952)
  nFloor := 321473977920922750767766599604171214694685989610481705707110400
  eFloor := 321390788526375435639523354331536688351096796484596198415532032
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1439809,width:=287961,den:=16384,localDen:=28334198897217871282176,lowerC:=28339268632925662347264,s:=[20863503116931072,-11960075196911616,3172404292608000],L:=[28341491206258917479475,-2906313384616001536,862584017499717632,-211850189588135936,33006239554207744],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor607Source.source.poly i) 1439809 287961 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor607Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 6) (CoreQuotient.fused G u 6 6) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 6 6 WideAnchor607Source.data
    WideAnchor607Source.path_checked WideAnchor607Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor607Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 6) (CoreQuotient.fused G u 6 6) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 6 6 WideAnchor607Source.data
    WideAnchor607Source.path_swapped WideAnchor607Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor607Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor607Cell131
