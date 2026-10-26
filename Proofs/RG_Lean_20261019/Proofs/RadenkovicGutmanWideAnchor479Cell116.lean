/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor479Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor479Cell116
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (23363/4096)
  b := (897139/131072)
  s := [(2690230574909/1125899906842624),(-5748840376091/4503599627370496),(718566105175/2251799813685248)]
  L := [(619732456843836939447/590295810358705651712),(-110327111693/6597069766656),(4337161503/1099511627776),(-303841177/412316860416),(6138129/68719476736)]
  c := (35611841595/34359738368)
  R := (1789636448527/100000000000000)
  total := (23820876151953/1000000000000000)
  k := 0
  n := 32
  sFloor := (1612303533473/2251799813685248)
  nFloor := 9557817177213276815894773760
  eFloor := 9060428716677212171315183616
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=747616,width:=149523,den:=131072,localDen:=1770887431076116955136,lowerC:=1835420340010289725440,s:=[4231366822973669376,-2260536017324998656,565103379224985600],L:=[1859197370531510818341,-29615708536473387008,6985487554820702208,-1304987918393147392,158178379881775104],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor479Source.source.poly i) 747616 149523 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor479Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 10) (CoreQuotient.fused G u 4 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 4 10 WideAnchor479Source.data
    WideAnchor479Source.path_checked WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 4) (CoreQuotient.fused G u 10 4) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 4 WideAnchor479Source.data
    WideAnchor479Source.path_swapped WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor479Cell116
