/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor020Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor020Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1669171/1048576)
  b := (500751/262144)
  s := [(3395293853341/70368744177664),(-1182018027133/70368744177664),(102028550685/35184372088832)]
  L := [(176129063716790590825/147573952589676412928),(-17278697237/13194139533312),(-59270870371/6597069766656),(2009598143/824633720832),(-128472737/412316860416)]
  c := (325820571269/274877906944)
  R := (4250495265799/50000000000000)
  total := (27742976496393/1000000000000000)
  k := 0
  n := 32
  sFloor := (1208666463789/70368744177664)
  nFloor := 666103431926152418662809600
  eFloor := 506731964167127737714081792
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1669171,width:=333833,den:=1048576,localDen:=442721857769029238784,lowerC:=524770761736647081984,s:=[21361341885365354496,-7436614408914075648,1283816274756894720],L:=[528387191150371772475,-579776871487504384,-3977600778889068544,1078894787785916416,-137946550960652288],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor020Source.source.poly i) 1669171 333833 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor020Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 29) (CoreQuotient.fused G u 9 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 29 WideAnchor020Source.data
    WideAnchor020Source.path_checked WideAnchor020Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor020Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 9) (CoreQuotient.fused G u 29 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 9 WideAnchor020Source.data
    WideAnchor020Source.path_swapped WideAnchor020Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor020Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor020Cell109
