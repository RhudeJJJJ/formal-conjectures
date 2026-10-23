/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (607573/274877906944)
  b := (334165/137438953472)
  s := [(4398045257089/4398046511104),(-250803/4398046511104),(-6269/2199023255552)]
  L := [(3669600689973/18446744073709551616),(2201748899725/55340232221128654848),(55043386415/27670116110564327424),(-799/3458764513820540928),(-11/1729382256910270464)]
  c := (917400172493/4611686018427387904)
  R := (-77151577937917/10000000000000)
  total := (-1694602683/1000000000000000)
  k := 23
  n := 32
  sFloor := (1099511248437/2199023255552)
  nFloor := (1615873000823/4722366482869645213696)
  eFloor := (579016410025/2361183241434822606848)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell067
