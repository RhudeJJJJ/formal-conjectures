/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor245Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor245Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (838683/17179869184)
  b := (1006419/17179869184)
  s := [(549753425735/549755813888),(-7641995/4398046511104),(-382079/2199023255552)]
  L := [(5553083531945/2305843009213693952),(6663629295203/6917529027641081856),(333170851699/3458764513820540928),(-235529/432345564227567616),(-5887/216172782113783808)]
  c := (694135441493/288230376151711744)
  R := (-161707544167653/25000000000000)
  total := (-62238246591/1000000000000000)
  k := 19
  n := 32
  sFloor := (2199009499863/4398046511104)
  nFloor := (752381843733/4611686018427387904)
  eFloor := (1357147622111/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=838683,width:=167736,den:=17179869184,localDen:=6917529027641081856,lowerC:=16659250595832,s:=[6917498977722040320,-12019818823680,-1201916608512],L:=[16659250595835,6663629295203,666341703398,-3768464,-188384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor245Source.source.poly i) 838683 167736 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor245Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 27) (CoreQuotient.fused G u 0 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 27 WideAnchor245Source.data
    WideAnchor245Source.path_checked WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 0) (CoreQuotient.fused G u 27 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 0 WideAnchor245Source.data
    WideAnchor245Source.path_swapped WideAnchor245Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor245Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor245Cell052
