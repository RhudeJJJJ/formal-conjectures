/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell080
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1048749/137438953472)
  b := (1153623/137438953472)
  s := [(549755409471/549755813888),(-647059/4398046511104),(-16177/2199023255552)]
  L := [(15994733525302733863182449159/41538374868278621028243970633760768),(2130906563227/27670116110564327424),(26636017369/6917529027641081856),(-2155/1729382256910270464),(-13/432345564227567616)]
  c := (1775772143253/4611686018427387904)
  R := (-738493437008343/100000000000000)
  total := (-174943829/31250000000000)
  k := 22
  n := 32
  sFloor := (2199021298177/4398046511104)
  nFloor := (51602603057/18446744073709551616)
  eFloor := (6161461817/2305843009213693952)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell080
