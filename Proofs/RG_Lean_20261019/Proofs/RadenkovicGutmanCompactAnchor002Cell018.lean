/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1457487/70368744177664)
  b := (1603235/70368744177664)
  s := [(549755813873/549755813888),(-27/4398046511104),(1/2199023255552)]
  L := [(3171090404612532423555997491/170141183460469231731687303715884105728),(844944161165/226673591177742970257408),(21123502555/113336795588871485128704),(1/3541774862152233910272),(-1/7083549724304467820544)]
  c := (1408247032147/75557863725914323419136)
  R := (-1235290945765639/100000000000000)
  total := (-25485133/1000000000000000)
  k := 36
  n := 32
  sFloor := (2199023255479/4398046511104)
  nFloor := (1052385457127/38685626227668133590597632)
  eFloor := (384291312391/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell018
