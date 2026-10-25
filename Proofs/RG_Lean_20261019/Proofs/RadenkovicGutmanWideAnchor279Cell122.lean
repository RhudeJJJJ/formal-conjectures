/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor279Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor279Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (558091/32768)
  b := (669709/32768)
  s := [(3606603883163/36028797018963968),(-256830785993/4503599627370496),(271080158941/18014398509481984)]
  L := [(74275801482419029361/73786976294838206464),(-34071595903/13194139533312),(4929473875/6597069766656),(-147547307/824633720832),(11277137/412316860416)]
  c := (1104611312635/1099511627776)
  R := (231370667463/100000000000000)
  total := (73554971461/7812500000000)
  k := 0
  n := 32
  sFloor := (2094117913101/72057594037927936)
  nFloor := 9031103956802058082844672
  eFloor := 8969872067842792839184384
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=558091,width:=111618,den:=32768,localDen:=221360928884514619392,lowerC:=222387631057451089920,s:=[22158974258153472,-12623746793127936,3331032993067008],L:=[222827404447257088083,-571626523929346048,165405695934464000,-39606928636116992,6054366825938944],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor279Source.source.poly i) 558091 111618 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor279Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 0 6 WideAnchor279Source.data
    WideAnchor279Source.path_checked WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 6 0 WideAnchor279Source.data
    WideAnchor279Source.path_swapped WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor279Cell122
