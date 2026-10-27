/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor028Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor028Cell108
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (10867/8192)
  b := (1669171/1048576)
  s := [(4604232365611/70368744177664),(-358304421047/17592186044416),(112139585959/35184372088832)]
  L := [(175118268081958111179/147573952589676412928),(220294906201/13194139533312),(-79147970611/6597069766656),(1973500271/824633720832),(-100061885/412316860416)]
  c := (652366385169/549755813888)
  R := (2139151745613/25000000000000)
  total := (11623813048539/500000000000000)
  k := 0
  n := 32
  sFloor := (848823463335/35184372088832)
  nFloor := 1580774228165816395759616000
  eFloor := 1168516711928678336383942656
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1390976,width:=278195,den:=1048576,localDen:=442721857769029238784,lowerC:=525354804245736456192,s:=[28967325342017519616,-9017025998490697728,1411042541838532608],L:=[525354804245874333537,7391870450067832832,-5311530395609595904,1059514890324017152,-107440630912778240],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor028Source.source.poly i) 1390976 278195 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor028Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 37) (CoreQuotient.fused G u 9 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 37 WideAnchor028Source.data
    WideAnchor028Source.path_checked WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 9) (CoreQuotient.fused G u 37 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 9 WideAnchor028Source.data
    WideAnchor028Source.path_swapped WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor028Cell108
