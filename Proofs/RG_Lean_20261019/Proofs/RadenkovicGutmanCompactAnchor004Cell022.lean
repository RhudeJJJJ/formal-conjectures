/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1066951/35184372088832)
  b := (586823/17592186044416)
  s := [(4398046510867/4398046511104),(-47/4398046511104),(-1/2199023255552)]
  L := [(2829117348541/75557863725914323419136),(848734409029/113336795588871485128704),(42436680701/113336795588871485128704),(-5/14167099448608935641088),(1/7083549724304467820544)]
  c := (707279337135/18889465931478580854784)
  R := (-75025624483111/6250000000000)
  total := (-7251019/200000000000000)
  k := 35
  n := 32
  sFloor := (2199023255409/4398046511104)
  nFloor := (155721745689/2417851639229258349412352)
  eFloor := (892797353231/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell022
