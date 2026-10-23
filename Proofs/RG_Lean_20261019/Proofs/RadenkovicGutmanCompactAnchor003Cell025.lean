/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1420111/35184372088832)
  b := (781061/17592186044416)
  s := [(4398046511011/4398046511104),(-17/4398046511104),(-1/2199023255552)]
  L := [(233433312063434850085538483/21267647932558653966460912964485513216),(995185364239/453347182355485940514816),(777488017/7083549724304467820544),(1/3541774862152233910272),(-1/7083549724304467820544)]
  c := (829321720855/75557863725914323419136)
  R := (-25235311722701/2000000000000)
  total := (-12682987/250000000000000)
  k := 37
  n := 32
  sFloor := (274877906937/549755813888)
  nFloor := (410626701167/4835703278458516698824704)
  eFloor := (785595446329/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell025
