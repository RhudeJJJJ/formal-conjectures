/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1173839/17179869184)
  b := (645611/8589934592)
  s := [(2198424357967/2199023255552),(-239458843/4398046511104),(-5974935/2199023255552)]
  L := [(481801077841390008084953733/2535301200456458802993406410752),(684484368309/18014398509481984),(17092895329/9007199254740992),(-238365/1125899906842624),(-2969/562949953421312)]
  c := (1711701279707/9007199254740992)
  R := (-428414583870297/100000000000000)
  total := (-28941172187/1000000000000000)
  k := 13
  n := 32
  sFloor := (1099149326805/2199023255552)
  nFloor := (753941358783/2305843009213693952)
  eFloor := (1080640514091/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell103
