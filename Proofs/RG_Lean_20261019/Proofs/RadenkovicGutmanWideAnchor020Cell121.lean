/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor020Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor020Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(3087981571439/18014398509481984),(-3499333208995/36028797018963968),(459590044509/18014398509481984)]
  L := [(297923819347270740725/295147905179352825856),(-47814531205/13194139533312),(2272778977/2199023255552),(-200929793/824633720832),(5055219/137438953472)]
  c := (1106777094477/1099511627776)
  R := (329308348943/100000000000000)
  total := (2786405320107/250000000000000)
  k := 0
  n := 32
  sFloor := (898952505725/18014398509481984)
  nFloor := 17985379782392624370914754801983257443590366251728998376286063665834197269125159025524261028626432
  eFloor := 17811692427521788112805746933844529354510454738705368283064878541262937896268229574192210909331456
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=885443715538058477568,lowerC:=891294642138865729536,s:=[151780470199369728,-85999612944261120,22589769867706368],L:=[893771458041812222175,-3208778871860101120,915141691617312768,-215746722431762432,32568000418676736],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor020Source.source.poly i) 465076 93015 32768
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
end Gebendorfer.RadenkovicGutman.WideAnchor020Cell121
