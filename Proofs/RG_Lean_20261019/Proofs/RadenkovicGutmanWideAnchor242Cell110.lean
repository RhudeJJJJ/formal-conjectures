/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor242Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor242Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (500751/262144)
  b := (600901/262144)
  s := [(1400318978077/35184372088832),(-2330622818321/140737488355328),(235476795289/70368744177664)]
  L := [(90143629163502669447/73786976294838206464),(-131676581495/4398046511104),(-17371968091/6597069766656),(553568097/274877906944),(-154870217/412316860416)]
  c := (1309231560517/1099511627776)
  R := (8728713180221/100000000000000)
  total := (55960969579/1562500000000)
  k := 0
  n := 32
  sFloor := (935401671141/70368744177664)
  nFloor := 819868411139134062592
  eFloor := 619727974171890679808
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=500751,width:=100150,den:=262144,localDen:=221360928884514619392,lowerC:=263583128217729368064,s:=[8810045236536410112,-3665752728515641344,740745948290875392],L:=[270430887490508008341,-6627499349649653760,-582906522015629312,445791913635741696,-83145314642427904],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor242Source.source.poly i) 500751 100150 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor242Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 24) (CoreQuotient.fused G u 0 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 24 WideAnchor242Source.data
    WideAnchor242Source.path_checked WideAnchor242Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor242Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 0) (CoreQuotient.fused G u 24 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 0 WideAnchor242Source.data
    WideAnchor242Source.path_swapped WideAnchor242Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor242Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor242Cell110
