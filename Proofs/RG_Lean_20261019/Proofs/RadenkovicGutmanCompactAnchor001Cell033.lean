/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (95129/1099511627776)
  b := (837135/8796093022208)
  s := [(137438953459/137438953472),(-21/1099511627776),(-1/1099511627776)]
  L := [(131601276964206053139935849/2658455991569831745807614120560689152),(280524256841/28334198897217871282176),(28052351929/56668397794435742564352),(1/1770887431076116955136),(-1/3541774862152233910272)]
  c := (1870166627273/37778931862957161709568)
  R := (-1186449494683847/100000000000000)
  total := (-102231731/1000000000000000)
  k := 35
  n := 32
  sFloor := (549755813825/1099511627776)
  nFloor := (869529465085/2417851639229258349412352)
  eFloor := (415294755161/1208925819614629174706176)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell033
