/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor537Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor537Cell111
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (600901/262144)
  b := (721081/262144)
  s := [(3325048816243/140737488355328),(-174399105219/17592186044416),(141729385469/70368744177664)]
  L := [(86048956901704644385/73786976294838206464),(-166440497863/6597069766656),(-1146963733/1099511627776),(277406597/206158430208),(-18310493/68719476736)]
  c := (1254528864607/1099511627776)
  R := (1318939889441/20000000000000)
  total := (511394459883/15625000000000)
  k := 0
  n := 32
  sFloor := (553328686357/70368744177664)
  nFloor := 517069799072383107072
  eFloor := 422919974252607176704
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=600901,width:=120180,den:=262144,localDen:=221360928884514619392,lowerC:=252570020876956729344,s:=[5229849581311229952,-2194448593849417728,445842096292626432],L:=[258146870705113933155,-5584816367590178816,-230914299512487936,297863065452412928,-58982226456477696],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor537Source.source.poly i) 600901 120180 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor537Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 15) (CoreQuotient.fused G u 5 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 15 WideAnchor537Source.data
    WideAnchor537Source.path_checked WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 5) (CoreQuotient.fused G u 15 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 5 WideAnchor537Source.data
    WideAnchor537Source.path_swapped WideAnchor537Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor537Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor537Cell111
