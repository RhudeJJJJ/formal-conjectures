/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell248
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (281101/4096)
  b := (309211/4096)
  s := [(3563826285243/2305843009213693952),(-2108347311703/4611686018427387904),(168307471103/2305843009213693952)]
  L := [(302358761449920900326023/302231454903657293676544),(-276640015/3298534883328),(20625959/1649267441664),(-667381/412316860416),(1997/12884901888)]
  c := (549947347161/549755813888)
  R := (17416815893/100000000000000)
  total := (1314258255039/1000000000000000)
  k := 0
  n := 32
  sFloor := (1338980050247/2305843009213693952)
  nFloor := 1291781624263725995867292980188590771330030687478571398361289259519942538286858240
  eFloor := 1291233735026665562000215407984033449497421477130731880322681695601417864882421760
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell248
