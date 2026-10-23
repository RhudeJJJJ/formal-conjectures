/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1153623/137438953472)
  b := (1268985/137438953472)
  s := [(4398024205015/4398046511104),(-2230587/2199023255552),(-27881/549755813888)]
  L := [(4402125703836708915306975459/1298074214633706907132624082305024),(293238200941/432345564227567616),(29323137767/864691128455135232),(-15173/216172782113783808),(-23/13510798882111488)]
  c := (1954936525477/576460752303423488)
  R := (-125943048119847/20000000000000)
  total := (-5245004279/1000000000000000)
  k := 19
  n := 32
  sFloor := (549752440099/1099511627776)
  nFloor := (1180050467527/295147905179352825856)
  eFloor := (882413972585/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell081
