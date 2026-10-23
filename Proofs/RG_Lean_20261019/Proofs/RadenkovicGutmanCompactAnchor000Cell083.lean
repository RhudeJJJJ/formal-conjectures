/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1395883/137438953472)
  b := (1535471/137438953472)
  s := [(4398013852915/4398046511104),(-6531553/4398046511104),(-163279/2199023255552)]
  L := [(805641140198862844802467089/162259276829213363391578010288128),(1717310695921/1729382256910270464),(42931375825/864691128455135232),(-16231/108086391056891904),(-205/54043195528445952)]
  c := (715553074747/144115188075855872)
  R := (-610653384009139/100000000000000)
  total := (-769106903/125000000000000)
  k := 18
  n := 32
  sFloor := (1099501748701/2199023255552)
  nFloor := (215963729861/36893488147419103232)
  eFloor := (322985191083/73786976294838206464)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell083
