/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor022Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor022Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (670803/1048576)
  b := (1609927/2097152)
  s := [(702754640563/4398046511104),(-1014742796007/35184372088832),(47804526943/17592186044416)]
  L := [(297258203565361147339/295147905179352825856),(941097010765/13194139533312),(-20878270483/2199023255552),(296606939/824633720832),(5529587/137438953472)]
  c := (138421637735/137438953472)
  R := (89056615097/25000000000000)
  total := (496780495991/200000000000000)
  k := 0
  n := 32
  sFloor := (1175725845595/17592186044416)
  nFloor := 885957605205
  eFloor := (1274556582595/2)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1341606,width:=268321,den:=2097152,localDen:=885443715538058477568,lowerC:=891774610695876771840,s:=[141483196796733751296,-25536838609580064768,2406080622901592064],L:=[891774610696083442017,63155951306234920960,-8406702086393167872,318479275692916736,35624092988080128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor022Source.source.poly i) 1341606 268321 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor022Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 31) (CoreQuotient.fused G u 9 31) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 31 WideAnchor022Source.data
    WideAnchor022Source.path_checked WideAnchor022Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor022Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 31 9) (CoreQuotient.fused G u 31 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 31 9 WideAnchor022Source.data
    WideAnchor022Source.path_swapped WideAnchor022Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor022Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor022Cell104
