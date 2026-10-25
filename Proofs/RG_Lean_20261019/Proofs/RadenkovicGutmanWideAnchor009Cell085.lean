/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor009Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor009Cell085
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (671899/33554432)
  b := (1612557/67108864)
  s := [(6055302859787/17592186044416),(-82218059935/2199023255552),(30210467723/4398046511104)]
  L := [(75805466104746076351/147573952589676412928),(598387338019/13194139533312),(-58092906913/6597069766656),(494282779/412316860416),(-45199133/412316860416)]
  c := (1129589469801/2199023255552)
  R := (-33307951068793/100000000000000)
  total := (-50311367367/40000000000000)
  k := 1
  n := 32
  sFloor := (1379600062799/8796093022208)
  nFloor := (976235025279/35184372088832)
  eFloor := (1854372607075/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1343798,width:=268759,den:=67108864,localDen:=442721857769029238784,lowerC:=227416398314122248192,s:=[152386686036096319488,-16552681807565291520,3041085254698795008],L:=[227416398314238229053,20078547243219550208,-3898548989389176832,530732092695248896,-48532199510638592],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor009Source.source.poly i) 1343798 268759 67108864
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
end Gebendorfer.RadenkovicGutman.WideAnchor009Cell085
