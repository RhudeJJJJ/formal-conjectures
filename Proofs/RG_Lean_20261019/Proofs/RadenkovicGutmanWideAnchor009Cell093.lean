/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor009Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor009Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (722259/8388608)
  b := (433355/4194304)
  s := [(4856114392825/17592186044416),(110999914135/17592186044416),(-8062801433/8796093022208)]
  L := [(373280012503365900163/590295810358705651712),(34176206207/26388279066624),(8807207981/13194139533312),(333700195/1649267441664),(-43188905/824633720832)]
  c := (347644102297/549755813888)
  R := (-22914747148737/100000000000000)
  total := (-393351715081/100000000000000)
  k := 1
  n := 32
  sFloor := (607014299103/4398046511104)
  nFloor := (1492548479903/1099511627776)
  eFloor := (1339107381363/1099511627776)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=722259,width:=144451,den:=8388608,localDen:=1770887431076116955136,lowerC:=1119840037509670109184,s:=[488832480534803251200,11173617212546088960,-1623256334478606336],L:=[1119840037510097700489,2293526374381518848,1182083445233287168,358307856048455680,-92747467262525440],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor009Source.source.poly i) 722259 144451 8388608
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor009Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 18) (CoreQuotient.fused G u 9 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 18 WideAnchor009Source.data
    WideAnchor009Source.path_checked WideAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor009Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 9) (CoreQuotient.fused G u 18 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 9 WideAnchor009Source.data
    WideAnchor009Source.path_swapped WideAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor009Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor009Cell093
