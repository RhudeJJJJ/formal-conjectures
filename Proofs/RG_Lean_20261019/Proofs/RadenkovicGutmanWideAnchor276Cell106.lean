/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor276Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor276Cell106
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241489/262144)
  b := (1159147/1048576)
  s := [(4992095401833/35184372088832),(-2837197792553/70368744177664),(213578007365/35184372088832)]
  L := [(167170798550905625089/147573952589676412928),(112471089257/1649267441664),(-22952019893/1099511627776),(1339619785/412316860416),(-21128389/68719476736)]
  c := (1245519508055/1099511627776)
  R := (3117165298959/50000000000000)
  total := (2743919334181/200000000000000)
  k := 0
  n := 32
  sFloor := (473384314115/8796093022208)
  nFloor := (404223187249/268435456)
  eFloor := (1072641444939/1073741824)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=965956,width:=193191,den:=1048576,localDen:=442721857769029238784,lowerC:=501512395652459397120,s:=[62815097136869277696,-17850105075144327168,2687433271809146880],L:=[501512395652716875267,30191228131519496192,-9241703889147789312,1438405791412387840,-136118609658249216],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor276Source.source.poly i) 965956 193191 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor276Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 0 4 WideAnchor276Source.data
    WideAnchor276Source.path_checked WideAnchor276Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor276Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 4 0 WideAnchor276Source.data
    WideAnchor276Source.path_swapped WideAnchor276Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor276Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor276Cell106
