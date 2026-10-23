/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (881779/35184372088832)
  b := (242489/8796093022208)
  s := [(274877906933/274877906944),(-35/4398046511104),(-1/2199023255552)]
  L := [(580348346807975567641573479/21267647932558653966460912964485513216),(154634284945/28334198897217871282176),(1932908831/7083549724304467820544),(7/14167099448608935641088),(-1/3541774862152233910272)]
  c := (2061811510173/75557863725914323419136)
  R := (-243245796363781/20000000000000)
  total := (-30359103/1000000000000000)
  k := 36
  n := 32
  sFloor := (2199023255445/4398046511104)
  nFloor := (770397664309/19342813113834066795298816)
  eFloor := (1125280200235/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell020
