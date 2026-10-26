/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor269Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor269Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(1965674335441/4611686018427387904),(-4508070429005/18446744073709551616),(597964965109/9223372036854775808)]
  L := [(9446423086933037596265/9444732965739290427392),(-470856389/6597069766656),(34966565/1649267441664),(-1074341/206158430208),(20935/25769803776)]
  c := (1099648382165/1099511627776)
  R := (62184829/1000000000000)
  total := (1573144561537/1000000000000000)
  k := 0
  n := 32
  sFloor := (142204901343/1152921504606846976)
  nFloor := 3675558953896785841808152843638454080065709857383862404342435863232663582855220495255684858936653891053613582548960645263583182441195567879251929976707622406999232209405456324308300296471669899264000
  eFloor := 3674898200308349913068252716371379942859700559547990483205317194922087656254439456550293887397782570173036444018019124899622818501575944617639589132680062285099687675250991086370305760724397561217024
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=28334198897217871282176,lowerC:=28337723030987908055040,s:=[12077103116949504,-6924396178951680,1836948372814848],L:=[28339269260799112788795,-2022312791867654144,600721012513832960,-147656302712061952,23018275927490560],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor269Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor269Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 45) (CoreQuotient.fused G u 0 45) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 45 WideAnchor269Source.data
    WideAnchor269Source.path_checked WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 45 0) (CoreQuotient.fused G u 45 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 45 0 WideAnchor269Source.data
    WideAnchor269Source.path_swapped WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor269Cell132
