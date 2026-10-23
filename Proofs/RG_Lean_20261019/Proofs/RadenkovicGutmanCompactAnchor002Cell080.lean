/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell080
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1048749/137438953472)
  b := (1153623/137438953472)
  s := [(4398030260259/4398046511104),(-3250125/4398046511104),(-81249/2199023255552)]
  L := [(5833120286061/2305843009213693952),(3499828925965/6917529027641081856),(87493651259/3458764513820540928),(-16525/432345564227567616),(-203/216172782113783808)]
  c := (1458280071515/576460752303423488)
  R := (-161092560362793/25000000000000)
  total := (-2439993669/500000000000000)
  k := 19
  n := 32
  sFloor := (1099506711909/2199023255552)
  nFloor := (68111209583/18446744073709551616)
  eFloor := (795892294853/295147905179352825856)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell080
