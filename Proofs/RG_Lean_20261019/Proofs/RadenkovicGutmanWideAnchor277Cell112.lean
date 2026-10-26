/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor277Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor277Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (721081/262144)
  b := (865297/262144)
  s := [(2427031859331/140737488355328),(-4615397488825/562949953421312),(522748222539/281474976710656)]
  L := [(10666260330554997061/9223372036854775808),(-82707701221/2199023255552),(3846259013/824633720832),(2148931/137438953472),(-2639569/25769803776)]
  c := (617598190373/549755813888)
  R := (1454548296491/25000000000000)
  total := (7166440106511/200000000000000)
  k := 0
  n := 32
  sFloor := (767278299197/140737488355328)
  nFloor := (598452672437/512)
  eFloor := (499950399449/512)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=721081,width:=144216,den:=262144,localDen:=27670116110564327424,lowerC:=31084734723290824704,s:=[477173879799349248,-226856017370726400,51388241268473856],L:=[31998780991664991183,-1040703726186135552,129059036506095616,432636954673152,-2834215632633856],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor277Source.source.poly i) 721081 144216 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor277Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 5) (CoreQuotient.fused G u 0 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 5 WideAnchor277Source.data
    WideAnchor277Source.path_checked WideAnchor277Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor277Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 0) (CoreQuotient.fused G u 5 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 0 WideAnchor277Source.data
    WideAnchor277Source.path_swapped WideAnchor277Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor277Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor277Cell112
