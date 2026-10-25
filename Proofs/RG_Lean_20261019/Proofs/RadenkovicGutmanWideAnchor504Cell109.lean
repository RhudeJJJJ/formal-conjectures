/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor504Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor504Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1669171/1048576)
  b := (500751/262144)
  s := [(6794601515099/140737488355328),(-2369561401553/140737488355328),(205251456591/70368744177664)]
  L := [(44036691621752753711/36893488147419103232),(-9604965487/6597069766656),(-4890934809/549755813888),(123970763/51539607552),(-5255057/17179869184)]
  c := (651660684681/549755813888)
  R := (4251244982503/50000000000000)
  total := (3469029629491/125000000000000)
  k := 0
  n := 32
  sFloor := (604442878341/35184372088832)
  nFloor := 666208467791053862232653824
  eFloor := 506731964167127737714081792
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1669171,width:=333833,den:=1048576,localDen:=110680464442257309696,lowerC:=131196624787212337152,s:=[5343492058722336768,-1863498912146128896,322832627019546624],L:=[132110074865258261133,-161144580647944192,-984675236790140928,266225186372583424,-33855446930423808],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor504Source.source.poly i) 1669171 333833 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor504Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 34) (CoreQuotient.fused G u 4 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 34 WideAnchor504Source.data
    WideAnchor504Source.path_checked WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 4) (CoreQuotient.fused G u 34 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 4 WideAnchor504Source.data
    WideAnchor504Source.path_swapped WideAnchor504Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor504Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor504Cell109
