/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell024
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (645505/17592186044416)
  b := (1420111/35184372088832)
  s := [(549755813841/549755813888),(-77/4398046511104),(-1/2199023255552)]
  L := [(1104914511867/18889465931478580854784),(2651794828267/226673591177742970257408),(66294870649/113336795588871485128704),(5/14167099448608935641088),(-1/7083549724304467820544)]
  c := (1104914511867/18889465931478580854784)
  R := (-589052556958919/50000000000000)
  total := (-8610051/200000000000000)
  k := 34
  n := 32
  sFloor := (549755813831/1099511627776)
  nFloor := (825704537047/9671406556917033397649408)
  eFloor := (1206064101475/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell024
