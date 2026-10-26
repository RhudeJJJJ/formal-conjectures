/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor538Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor538Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (501569/8388608)
  b := (1203765/16777216)
  s := [(3206672174195/17592186044416),(237395680641/35184372088832),(9797147661/17592186044416)]
  L := [(108596519310140977793/147573952589676412928),(-18677180959/6597069766656),(-594685567/412316860416),(502361681/824633720832),(-19684633/206158430208)]
  c := (804973258859/1099511627776)
  R := (-3118123273933/20000000000000)
  total := (-462023935029/250000000000000)
  k := 1
  n := 32
  sFloor := (1603336087097/17592186044416)
  nFloor := (1175088220697/4398046511104)
  eFloor := (1104460342285/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1003138,width:=200627,den:=16777216,localDen:=442721857769029238784,lowerC:=324125045714432557056,s:=[80698547561488711680,2987128958685806592,246553293738737664],L:=[325789557930422933379,-1253404396880920576,-638538765417054208,269703373832323072,-42272427484381184],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor538Source.source.poly i) 1003138 200627 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor538Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 16) (CoreQuotient.fused G u 5 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 16 WideAnchor538Source.data
    WideAnchor538Source.path_checked WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 5) (CoreQuotient.fused G u 16 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 5 WideAnchor538Source.data
    WideAnchor538Source.path_swapped WideAnchor538Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor538Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor538Cell091
