/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor520Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor520Cell107
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1159147/1048576)
  b := (10867/8192)
  s := [(6049364601259/70368744177664),(-1679380063145/70368744177664),(119915388609/35184372088832)]
  L := [(171675164376589986711/147573952589676412928),(463256599105/13194139533312),(-29480369607/2199023255552),(1670322341/824633720832),(-21984381/137438953472)]
  c := (1279079648677/1099511627776)
  R := (3781867209227/50000000000000)
  total := (4500489671607/250000000000000)
  k := 0
  n := 32
  sFloor := (1152453828833/35184372088832)
  nFloor := (631834344067/524288)
  eFloor := (228570944001/262144)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1159147,width:=231829,den:=1048576,localDen:=442721857769029238784,lowerC:=515025493129395437568,s:=[38059311216778543104,-10565745774553989120,1508884782312849408],L:=[515025493129769960133,15544312053219983360,-5935182343877689344,896747478546644992,-70816648063352832],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor520Source.source.poly i) 1159147 231829 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor520Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 5) (CoreQuotient.fused G u 4 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 5 WideAnchor520Source.data
    WideAnchor520Source.path_checked WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 4) (CoreQuotient.fused G u 5 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 4 WideAnchor520Source.data
    WideAnchor520Source.path_swapped WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor520Cell107
