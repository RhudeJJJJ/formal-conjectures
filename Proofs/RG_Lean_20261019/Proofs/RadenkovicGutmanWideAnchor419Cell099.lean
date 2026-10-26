/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor419Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor419Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (269581/1048576)
  b := (323497/1048576)
  s := [(4339470306517/8796093022208),(-765006900425/8796093022208),(41866644463/4398046511104)]
  L := [(122922666236807679889/295147905179352825856),(5980569712967/52776558133248),(-94452485785/26388279066624),(-3476153177/3298534883328),(276951829/1649267441664)]
  c := (457922615993/1099511627776)
  R := (-43796058816333/100000000000000)
  total := (-2421965231033/125000000000000)
  k := 2
  n := 32
  sFloor := (1829098347509/8796093022208)
  nFloor := (2073880625167/549755813888)
  eFloor := (1689462659347/549755813888)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=269581,width:=53916,den:=1048576,localDen:=885443715538058477568,lowerC:=368767998710381543424,s:=[436825383948131500032,-77008116059524300800,8428868848211460096],L:=[368767998710423039667,100337309877505359872,-3169299511503749120,-933122763193843712,148687381015298048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor419Source.source.poly i) 269581 53916 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor419Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 4 WideAnchor419Source.data
    WideAnchor419Source.path_checked WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 2 WideAnchor419Source.data
    WideAnchor419Source.path_swapped WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor419Cell099
