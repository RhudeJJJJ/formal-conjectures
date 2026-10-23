/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (47157/34359738368)
  b := (829963/549755813888)
  s := [(1099511478685/1099511627776),(-14909/549755813888),(-1491/1099511627776)]
  L := [(470770372565784769540959361/5192296858534827628530496329220096),(334501535553/18446744073709551616),(25087534813/27670116110564327424),(-59/1152921504606846976),(-1/1729382256910270464)]
  c := (418128085547/4611686018427387904)
  R := (-810803577371517/100000000000000)
  total := (-1106140403/1000000000000000)
  k := 24
  n := 32
  sFloor := (68719465461/137438953472)
  nFloor := (1009566811997/9444732965739290427392)
  eFloor := (1509860611885/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell062
