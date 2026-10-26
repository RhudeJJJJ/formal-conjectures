/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor425Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor425Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (500751/262144)
  b := (600901/262144)
  s := [(4794282422065/140737488355328),(-463663061365/35184372088832),(2764111517/1099511627776)]
  L := [(10856296723738627529/9223372036854775808),(-87892394155/6597069766656),(-17269007171/3298534883328),(825049945/412316860416),(-63565813/206158430208)]
  c := (1275627467023/1099511627776)
  R := (371430205207/5000000000000)
  total := (29838083467109/1000000000000000)
  k := 0
  n := 32
  sFloor := (823359112695/70368744177664)
  nFloor := (623653894817/512)
  eFloor := (247469279005/256)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=500751,width:=100150,den:=262144,localDen:=27670116110564327424,lowerC:=32102216324666621952,s:=[942594278437355520,-364639468675399680,69561143953195008],L:=[32568890171215882587,-368647420373893120,-144862931706707968,55368164552212480,-8531658999332864],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor425Source.source.poly i) 500751 100150 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor425Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 6 WideAnchor425Source.data
    WideAnchor425Source.path_checked WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 6 2 WideAnchor425Source.data
    WideAnchor425Source.path_swapped WideAnchor425Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor425Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor425Cell110
