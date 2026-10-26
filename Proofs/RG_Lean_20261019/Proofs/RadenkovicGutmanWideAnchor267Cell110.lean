/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor267Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor267Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (500751/262144)
  b := (600901/262144)
  s := [(1400318978077/35184372088832),(-2330622818321/140737488355328),(235476795289/70368744177664)]
  L := [(45071814810918116489/36893488147419103232),(-131676581511/4398046511104),(-17371967987/6597069766656),(553568091/274877906944),(-154870213/412316860416)]
  c := (1309231567347/1099511627776)
  R := (8728713441061/100000000000000)
  total := (35815021514259/1000000000000000)
  k := 0
  n := 32
  sFloor := (935401671141/70368744177664)
  nFloor := 85215147604530853119708287020826624
  eFloor := 64413032721084630889345118290051072
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=500751,width:=100150,den:=262144,localDen:=110680464442257309696,lowerC:=131791564796394995712,s:=[4405022618268205056,-1832876364257820672,370372974145437696],L:=[135215444432754349467,-3313749675227480064,-291453259262984192,222895954401951744,-41572656247472128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor267Source.source.poly i) 500751 100150 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor267Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 43) (CoreQuotient.fused G u 0 43) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 43 WideAnchor267Source.data
    WideAnchor267Source.path_checked WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 43 0) (CoreQuotient.fused G u 43 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 43 0 WideAnchor267Source.data
    WideAnchor267Source.path_swapped WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor267Cell110
