/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor025Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor025Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (584323/17592186044416)
  b := (1402375/35184372088832)
  s := [(1099511627747/1099511627776),(-45/4398046511104),(-3/2199023255552)]
  L := [(4317628515319/302231454903657293676544),(1727049928263/302231454903657293676544),(259057267513/453347182355485940514816),(1/18889465931478580854784),(-1/28334198897217871282176)]
  c := (2158814257659/151115727451828646838272)
  R := (-312146908387619/25000000000000)
  total := (-82320737/1000000000000000)
  k := 37
  n := 32
  sFloor := (549755813867/1099511627776)
  nFloor := (1080935881677/9671406556917033397649408)
  eFloor := (62138402973/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1168646,width:=233729,den:=35184372088832,localDen:=906694364710971881029632,lowerC:=12952885545954,s:=[906694364687057503125504,-9277129359360,-1236950581248],L:=[12952885545957,5181149784789,518114535026,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor025Source.source.poly i) 1168646 233729 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor025Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 34) (CoreQuotient.fused G u 9 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 34 WideAnchor025Source.data
    WideAnchor025Source.path_checked WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 9) (CoreQuotient.fused G u 34 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 9 WideAnchor025Source.data
    WideAnchor025Source.path_swapped WideAnchor025Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor025Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor025Cell012
