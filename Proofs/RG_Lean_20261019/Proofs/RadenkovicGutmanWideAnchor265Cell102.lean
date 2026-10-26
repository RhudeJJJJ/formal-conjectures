/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor265Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor265Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (931671/2097152)
  b := (1118005/2097152)
  s := [(1358661131119/4398046511104),(-839917409647/17592186044416),(35033284049/8796093022208)]
  L := [(512573643808964681335/590295810358705651712),(231286729297/2199023255552),(-32872928017/3298534883328),(22594235/137438953472),(8763073/206158430208)]
  c := (7458928213/8589934592)
  R := (-882371180109/12500000000000)
  total := (-1918996462479/500000000000000)
  k := 1
  n := 32
  sFloor := (1166198420731/8796093022208)
  nFloor := (589444558613/2048)
  eFloor := (1433599916673/8192)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=931671,width:=186334,den:=2097152,localDen:=1770887431076116955136,lowerC:=1537720931426242658304,s:=[547069230422106832896,-84548854822849216512,7053131684153131008],L:=[1537720931426894044005,186256675936766263296,-17648518844597141504,291124501209415680,75274223894921216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor265Source.source.poly i) 931671 186334 2097152
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
end Gebendorfer.RadenkovicGutman.WideAnchor265Cell102
