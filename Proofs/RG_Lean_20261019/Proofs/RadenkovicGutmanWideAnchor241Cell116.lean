/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor241Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor241Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (23363/4096)
  b := (897139/131072)
  s := [(1387014004403/562949953421312),(-3017822870559/2251799813685248),(383016948509/1125899906842624)]
  L := [(155199246808460666555/147573952589676412928),(-237699508709/13194139533312),(29721070381/6597069766656),(-751746223/824633720832),(49596923/412316860416)]
  c := (570299823215/549755813888)
  R := (7337604657/400000000000)
  total := (24534810965381/1000000000000000)
  k := 0
  n := 32
  sFloor := (1648133522035/2251799813685248)
  nFloor := 664057571848151655010095024914780622159872
  eFloor := 628327031669331247112276087069125682135040
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=747616,width:=149523,den:=131072,localDen:=442721857769029238784,lowerC:=459266079304313733120,s:=[1090792197510660096,-593328118934863872,150608392424914944],L:=[465597740425381999665,-7975872001409548288,1994547270132957184,-403590680334565376,53254290566807552],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor241Source.source.poly i) 747616 149523 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor241Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 23) (CoreQuotient.fused G u 0 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 23 WideAnchor241Source.data
    WideAnchor241Source.path_checked WideAnchor241Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor241Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 0) (CoreQuotient.fused G u 23 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 0 WideAnchor241Source.data
    WideAnchor241Source.path_swapped WideAnchor241Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor241Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor241Cell116
