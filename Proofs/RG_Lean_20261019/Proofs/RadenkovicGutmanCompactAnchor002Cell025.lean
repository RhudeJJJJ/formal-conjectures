/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1420111/35184372088832)
  b := (781061/17592186044416)
  s := [(4398046510649/4398046511104),(-23/1099511627776),(-1/1099511627776)]
  L := [(5347786237339/75557863725914323419136),(3208669482551/226673591177742970257408),(80216680675/113336795588871485128704),(-23/14167099448608935641088),(5/7083549724304467820544)]
  c := (668473279667/9444732965739290427392)
  R := (-1168574095938343/100000000000000)
  total := (-46970557/1000000000000000)
  k := 34
  n := 32
  sFloor := (549755813819/1099511627776)
  nFloor := (999102489827/9671406556917033397649408)
  eFloor := (1459337562785/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell025
