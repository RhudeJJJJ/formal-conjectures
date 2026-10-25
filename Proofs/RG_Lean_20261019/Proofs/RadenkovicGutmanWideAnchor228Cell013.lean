/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor228Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor228Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1402375/35184372088832)
  b := (841425/17592186044416)
  s := [(4398046511103/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(1322035291265/19342813113834066795298816),(3172884699053/116056878683004400771792896),(158644234927/58028439341502200385896448),(1/1813388729421943762059264),(-1/3626777458843887524118528)]
  c := (1322035291265/19342813113834066795298816)
  R := (-1515708480733719/100000000000000)
  total := (-120078703/1000000000000000)
  k := 44
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (727321105491/19342813113834066795298816)
  eFloor := (903044844477/19342813113834066795298816)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1402375,width:=280475,den:=35184372088832,localDen:=116056878683004400771792896,lowerC:=7932211747590,s:=[116056878682978012492726272,26388279066624,-52776558133248],L:=[7932211747590,3172884699053,317288469854,64,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor228Source.source.poly i) 1402375 280475 35184372088832
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor228Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 12) (CoreQuotient.fused G u 0 12) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 0 12 WideAnchor228Source.data
    WideAnchor228Source.path_checked WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 0) (CoreQuotient.fused G u 12 0) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 12 0 WideAnchor228Source.data
    WideAnchor228Source.path_swapped WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor228Cell013
