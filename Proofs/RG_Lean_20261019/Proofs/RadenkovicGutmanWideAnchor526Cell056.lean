/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor526Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor526Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (869545/8589934592)
  b := (521727/4294967296)
  s := [(4398044892851/4398046511104),(-323649/2199023255552),(-16183/1099511627776)]
  L := [(627054992063734791462378969/10384593717069655257060992658440192),(891099136789/36893488147419103232),(66832554565/27670116110564327424),(995/1152921504606846976),(37/864691128455135232)]
  c := (139234177979/2305843009213693952)
  R := (-207781936599869/25000000000000)
  total := (-41592430381/250000000000000)
  k := 24
  n := 32
  sFloor := (1099511045205/2199023255552)
  nFloor := (49019071981/576460752303423488)
  eFloor := (149350073981/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=869545,width:=173909,den:=8589934592,localDen:=31153781151208965771182977975320576,lowerC:=1881164976190385159512522752,s:=[31153769688233373766305013976530944,-4585167569442833411302490112,-458532340753676810959454208],L:=[1881164976191204374387136907,752466326323708320653770752,75246766958788085347778560,26886489775401861120,1333065489701666816],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor526Source.source.poly i) 869545 173909 8589934592
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
end Gebendorfer.RadenkovicGutman.WideAnchor526Cell056
