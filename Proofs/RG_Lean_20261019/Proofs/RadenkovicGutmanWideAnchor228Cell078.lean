/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor228Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor228Cell078
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (750061/134217728)
  b := (900073/134217728)
  s := [(4383483235971/4398046511104),(-5783299057/4398046511104),(-277676085/2199023255552)]
  L := [(103440461536610138255229/77371252455336267181195264),(2396493883057/4503599627370496),(352373042659/6755399441055744),(-58445531/281474976710656),(-4000975/422212465065984)]
  c := (1505256827463/1125899906842624)
  R := (-330868718947489/100000000000000)
  total := (-3593861490707/1000000000000000)
  k := 10
  n := 32
  sFloor := (547143073093/1099511627776)
  nFloor := (1668332525913/2251799813685248)
  eFloor := (64671166341/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=750061,width:=150012,den:=134217728,localDen:=232113757366008801543585792,lowerC:=310321384609646383202304,s:=[231345157829341542044663808,-305222618883718838747136,-29309576084430425948160],L:=[310321384609830414765687,123514354233526362046464,12107445553699343040512,-48196155694532001792,-2199559267470540800],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor228Source.source.poly i) 750061 150012 134217728
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor228Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 12) (CoreQuotient.fused G u 0 12) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 0 12 WideAnchor228Source.data
    WideAnchor228Source.path_checked WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 0) (CoreQuotient.fused G u 12 0) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 12 0 WideAnchor228Source.data
    WideAnchor228Source.path_swapped WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor228Cell078
