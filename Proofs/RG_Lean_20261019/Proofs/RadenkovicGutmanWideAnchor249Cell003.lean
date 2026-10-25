/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor249Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor249Cell003
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (905969/140737488355328)
  b := (543581/70368744177664)
  s := [(4398046511103/4398046511104)]
  L := [(239837540630106622482262207/696898287454081973172991196020261297061888),(681656279397/4951760157141521099596496896),(68165326957/4951760157141521099596496896),(1/154742504910672534362390528),(-1/309485009821345068724781056)]
  c := (426037055643/1237940039285380274899124224)
  R := (-1780272704294241/100000000000000)
  total := (-2849939/125000000000000)
  k := 52
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (253734327469/309485009821345068724781056)
  eFloor := (69497598777/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=905969,width:=181193,den:=140737488355328,localDen:=696898287454081973172991196020261297061888,lowerC:=239837540629979758766063616,s:=[696898287453923516847962667345074209161216],L:=[239837540630106622482262207,95934592683971497181577216,9593416908847913312976896,4503599627370496,-2251799813685248],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor249Source.source.poly i) 905969 181193 140737488355328
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor249Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 2 WideAnchor249Source.data
    WideAnchor249Source.path_checked WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 0 WideAnchor249Source.data
    WideAnchor249Source.path_swapped WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor249Cell003
