/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1104679/549755813888)
  b := (607573/274877906944)
  s := [(4398045384199/4398046511104),(-56345/1099511627776),(-2817/1099511627776)]
  L := [(3235948036497/18446744073709551616),(1941552495415/55340232221128654848),(16179455363/9223372036854775808),(-631/3458764513820540928),(-3/576460752303423488)]
  c := (202246752281/1152921504606846976)
  R := (-777803824939189/100000000000000)
  total := (-1553179213/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022573775/4398046511104)
  nFloor := (1209115115577/4722366482869645213696)
  eFloor := (1766092191709/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell066
