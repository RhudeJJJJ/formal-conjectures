/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (95129/1099511627776)
  b := (837135/8796093022208)
  s := [(4398046510679/4398046511104),(-83/4398046511104),(-3/2199023255552)]
  L := [(3810695760607/75557863725914323419136),(2286411447409/226673591177742970257408),(57160135909/113336795588871485128704),(5/14167099448608935641088),(-1/7083549724304467820544)]
  c := (1905347880303/37778931862957161709568)
  R := (-1185517640991419/100000000000000)
  total := (-102151107/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255295/4398046511104)
  nFloor := (471702775325/1208925819614629174706176)
  eFloor := (28201371165/75557863725914323419136)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell033
