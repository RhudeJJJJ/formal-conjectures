/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor531Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor531Cell088
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (72565/2097152)
  b := (43539/1048576)
  s := [(3754892012287/35184372088832),(-2631265335/1099511627776),(15190998099/8796093022208)]
  L := [(295897595111687631553/295147905179352825856),(1722305389/549755813888),(-3961046195/824633720832),(124329019/137438953472),(-11638907/103079215104)]
  c := (1101338140069/1099511627776)
  R := (82991249063/100000000000000)
  total := (146255753/15625000000000)
  k := 0
  n := 32
  sFloor := (1856395883463/35184372088832)
  nFloor := (484203362039/8796093022208)
  eFloor := (779660430275/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=72565,width:=14513,den:=2097152,localDen:=885443715538058477568,lowerC:=886914617518841659392,s:=[94494951520220479488,-2118974730173153280,1529175938175074304],L:=[887692785335062894659,2773966994804834304,-4253140966367559680,800983605823143936,-99977449852370944],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor531Source.source.poly i) 72565 14513 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor531Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 9) (CoreQuotient.fused G u 5 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 9 WideAnchor531Source.data
    WideAnchor531Source.path_checked WideAnchor531Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor531Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 5) (CoreQuotient.fused G u 9 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 5 WideAnchor531Source.data
    WideAnchor531Source.path_swapped WideAnchor531Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor531Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor531Cell088
