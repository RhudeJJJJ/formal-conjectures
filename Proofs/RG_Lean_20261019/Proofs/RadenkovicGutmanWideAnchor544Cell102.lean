/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor544Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor544Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (931671/2097152)
  b := (1118005/2097152)
  s := [(7057137372039/35184372088832),(-359811666971/17592186044416),(4351911/68719476736)]
  L := [(130540434170801237715/147573952589676412928),(818138397883/13194139533312),(-8538035603/6597069766656),(-789634651/824633720832),(62687843/412316860416)]
  c := (1945204051893/2199023255552)
  R := (-6132320223131/100000000000000)
  total := (-989312976721/250000000000000)
  k := 1
  n := 32
  sFloor := (396233888533/4398046511104)
  nFloor := (254740200385/524288)
  eFloor := (191756331343/524288)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=931671,width:=186334,den:=2097152,localDen:=442721857769029238784,lowerC:=391621302512208838656,s:=[88799338524277997568,-9054957084138799104,28036973130153984],L:=[391621302512403713145,27452169238354067456,-572977870108884992,-423931875229171712,67310558885445632],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor544Source.source.poly i) 931671 186334 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor544Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 22) (CoreQuotient.fused G u 5 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 22 WideAnchor544Source.data
    WideAnchor544Source.path_checked WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 5) (CoreQuotient.fused G u 22 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 5 WideAnchor544Source.data
    WideAnchor544Source.path_swapped WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor544Cell102
