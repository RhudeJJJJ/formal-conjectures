/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor282Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor282Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (139979/8388608)
  b := (671899/33554432)
  s := [(4364017699585/4398046511104),(-26911121431/8796093022208),(-1261011557/4398046511104)]
  L := [(27199263448416296614875/4835703278458516698824704),(7543299178463/3377699720527872),(366057362995/1688849860263936),(-272763065/211106232532992),(-5967511/105553116266496)]
  c := (1583205503901/281474976710656)
  R := (-51805919592079/20000000000000)
  total := (-8334506686331/1000000000000000)
  k := 8
  n := 32
  sFloor := (271831320457/549755813888)
  nFloor := (660267856681/70368744177664)
  eFloor := (455893086015/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=559916,width:=111983,den:=33554432,localDen:=14507109835375550096474112,lowerC:=81597790345223945060352,s:=[14394864613541934929018880,-44383636394814612701184,-4159490609044254621696],L:=[81597790345248889844625,32398223275442252546048,3144408805047051223040,-18744135099707555840,-820168466672648192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor282Source.source.poly i) 559916 111983 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor282Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 8 WideAnchor282Source.data
    WideAnchor282Source.path_checked WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 8 0 WideAnchor282Source.data
    WideAnchor282Source.path_swapped WideAnchor282Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor282Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor282Cell084
