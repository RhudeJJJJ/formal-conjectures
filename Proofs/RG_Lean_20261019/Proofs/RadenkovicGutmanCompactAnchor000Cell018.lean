/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1457487/70368744177664)
  b := (1603235/70368744177664)
  s := [(549755813871/549755813888),(-27/4398046511104),(-1/2199023255552)]
  L := [(1560222285441/75557863725914323419136),(936128875181/226673591177742970257408),(11701554745/56668397794435742564352),(-7/28334198897217871282176),(1/7083549724304467820544)]
  c := (1560222285441/75557863725914323419136)
  R := (-1230166815242469/100000000000000)
  total := (-12689501/500000000000000)
  k := 36
  n := 32
  sFloor := (2199023255469/4398046511104)
  nFloor := (470892913975/19342813113834066795298816)
  eFloor := (1408490562017/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell018
