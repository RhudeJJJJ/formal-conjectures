/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor265Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor265Cell050
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (582419/17179869184)
  b := (1397805/34359738368)
  s := [(4398041379249/4398046511104),(-513183/1099511627776),(-51317/1099511627776)]
  L := [(743598549477/1152921504606846976),(594875927029/2305843009213693952),(89230330981/3458764513820540928),(-6903/144115188075855872),(-517/216172782113783808)]
  c := (743598549477/1152921504606846976)
  R := (-178175796143517/25000000000000)
  total := (-1192185131/25000000000000)
  k := 21
  n := 32
  sFloor := (137438722539/274877906944)
  nFloor := (523063006899/4611686018427387904)
  eFloor := (473151233927/4611686018427387904)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1164838,width:=232967,den:=34359738368,localDen:=6917529027641081856,lowerC:=4461591296862,s:=[6917520955931099136,-3228668264448,-322858647552],L:=[4461591296862,1784627781087,178460661962,-331344,-16544],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor265Source.source.poly i) 1164838 232967 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor265Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 41) (CoreQuotient.fused G u 0 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 41 WideAnchor265Source.data
    WideAnchor265Source.path_checked WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 0) (CoreQuotient.fused G u 41 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 0 WideAnchor265Source.data
    WideAnchor265Source.path_swapped WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor265Cell050
