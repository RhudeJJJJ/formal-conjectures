/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor533Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor533Cell089
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (43539/1048576)
  b := (1671897/33554432)
  s := [(7876325964907/70368744177664),(96849517429/70368744177664),(51376069315/35184372088832)]
  L := [(147789663519710916129/147573952589676412928),(-84595354585/13194139533312),(-9251596757/2199023255552),(709325479/824633720832),(-14456303/137438953472)]
  c := (2180547010133/2199023255552)
  R := (-421875981227/100000000000000)
  total := (-12294562447/1000000000000000)
  k := 1
  n := 32
  sFloor := (984540745613/17592186044416)
  nFloor := (821868605317/8796093022208)
  eFloor := (1310896351317/17592186044416)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1393248,width:=278649,den:=33554432,localDen:=442721857769029238784,lowerC:=439002098245866356736,s:=[49553558249869934592,609324477525786624,646460559096545280],L:=[443368990559132748387,-2838549072938270720,-1862592445645062144,380816216815566848,-46567011454550016],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor533Source.source.poly i) 1393248 278649 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor533Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 11) (CoreQuotient.fused G u 5 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 11 WideAnchor533Source.data
    WideAnchor533Source.path_checked WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 5) (CoreQuotient.fused G u 11 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 5 WideAnchor533Source.data
    WideAnchor533Source.path_swapped WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor533Cell089
