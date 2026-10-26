/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor526Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor526Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (672997/1073741824)
  b := (201899/268435456)
  s := [(2198992236409/2199023255552),(-3101845/549755813888),(-620301/1099511627776)]
  L := [(2668979283343/1152921504606846976),(3202820421091/3458764513820540928),(160151504681/1729382256910270464),(273977/216172782113783808),(6847/108086391056891904)]
  c := (1334489641671/576460752303423488)
  R := (-162201420115387/25000000000000)
  total := (-160312178503/200000000000000)
  k := 19
  n := 32
  sFloor := (2198978588427/4398046511104)
  nFloor := (939670504597/288230376151711744)
  eFloor := (178930008785/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=672997,width:=134599,den:=1073741824,localDen:=3458764513820540928,lowerC:=8006937850026,s:=[3458715724927205376,-19515121336320,-1951298224128],L:=[8006937850029,3202820421091,320303009362,4383632,219104],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor526Source.source.poly i) 672997 134599 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor526Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 4 6 WideAnchor526Source.data
    WideAnchor526Source.path_checked WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 4 WideAnchor526Source.data
    WideAnchor526Source.path_swapped WideAnchor526Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor526Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor526Cell066
