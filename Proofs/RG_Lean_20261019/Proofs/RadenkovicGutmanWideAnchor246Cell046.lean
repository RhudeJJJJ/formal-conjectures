/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor246Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor246Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1123495/68719476736)
  b := (674097/34359738368)
  s := [(4398046206787/4398046511104),(-121729/4398046511104),(-6085/2199023255552)]
  L := [(5043409188203/147573952589676412928),(2017363425019/147573952589676412928),(302604363529/221360928884514619392),(-1247/9223372036854775808),(-97/13835058055282163712)]
  c := (630426148525/18446744073709551616)
  R := (-859587885097373/100000000000000)
  total := (-13900162557/500000000000000)
  k := 25
  n := 32
  sFloor := (549755759111/1099511627776)
  nFloor := (602659535409/36893488147419103232)
  eFloor := (1220178841059/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1123495,width:=224699,den:=68719476736,localDen:=442721857769029238784,lowerC:=15130227564600,s:=[442721827135476989952,-12253642358784,-1225072312320],L:=[15130227564609,6052090275057,605208727058,-59856,-3104],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor246Source.source.poly i) 1123495 224699 68719476736
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
end Gebendorfer.RadenkovicGutman.WideAnchor246Cell046
