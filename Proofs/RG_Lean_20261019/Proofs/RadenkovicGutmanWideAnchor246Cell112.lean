/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor246Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor246Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (721081/262144)
  b := (865297/262144)
  s := [(606758744403/35184372088832),(-576927587141/70368744177664),(261377118733/140737488355328)]
  L := [(170660198279137031779/147573952589676412928),(-15507877645/412316860416),(1923324905/412316860416),(6328783/412316860416),(-10550357/103079215104)]
  c := (1235196427605/1099511627776)
  R := (1454548770697/25000000000000)
  total := (4479028151451/125000000000000)
  k := 0
  n := 32
  sFloor := (1534556922063/281474976710656)
  nFloor := 32734726785279992041672494022656
  eFloor := 27346750745268781160009880829952
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=721081,width:=144216,den:=262144,localDen:=442721857769029238784,lowerC:=497355774440578744320,s:=[7634791886053441536,-3629714529683767296,822221320957722624],L:=[511980594837411095337,-16651456828911124480,2065154391639326720,6795479002120192,-45313438276124672],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor246Source.source.poly i) 721081 144216 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor246Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 28) (CoreQuotient.fused G u 0 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 28 WideAnchor246Source.data
    WideAnchor246Source.path_checked WideAnchor246Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor246Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 0) (CoreQuotient.fused G u 28 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 0 WideAnchor246Source.data
    WideAnchor246Source.path_swapped WideAnchor246Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor246Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor246Cell112
