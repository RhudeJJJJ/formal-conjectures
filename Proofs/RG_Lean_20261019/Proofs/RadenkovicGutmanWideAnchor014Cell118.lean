/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor014Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor014Cell118
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (538283/65536)
  b := (1291879/131072)
  s := [(1916516489081/2251799813685248),(-4245552239185/9007199254740992),(547007222841/4503599627370496)]
  L := [(37866407034829732393/36893488147419103232),(-127188707315/13194139533312),(16943479663/6597069766656),(-462476515/824633720832),(32714813/412316860416)]
  c := (1120202328597/1099511627776)
  R := (932160652771/100000000000000)
  total := (9049678836911/500000000000000)
  k := 0
  n := 32
  sFloor := (1128632040705/4503599627370496)
  nFloor := 3982391557494735418432008362679400627005468268088371224485029740544
  eFloor := 3873470875472061605388864855554896705612095192787873258840090738688
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1076566,width:=215313,den:=131072,localDen:=110680464442257309696,lowerC:=112763258583449075712,s:=[94200618471309312,-52169345915105280,13443249508540416],L:=[113599221104489197179,-1066936207692267520,284264418097758208,-62072547096657920,8781815745609728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor014Source.source.poly i) 1076566 215313 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor014Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 23) (CoreQuotient.fused G u 9 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 23 WideAnchor014Source.data
    WideAnchor014Source.path_checked WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 9) (CoreQuotient.fused G u 23 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 9 WideAnchor014Source.data
    WideAnchor014Source.path_swapped WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor014Cell118
