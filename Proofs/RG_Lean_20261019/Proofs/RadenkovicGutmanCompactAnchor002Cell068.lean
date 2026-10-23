/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell068
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (334165/137438953472)
  b := (735163/274877906944)
  s := [(2199022430603/2199023255552),(-164989/2199023255552),(-4125/1099511627776)]
  L := [(4737739673299/18446744073709551616),(2842642714529/55340232221128654848),(71065959035/27670116110564327424),(-1385/3458764513820540928),(-11/1729382256910270464)]
  c := (296108729581/1152921504606846976)
  R := (-758741914005487/100000000000000)
  total := (-916506633/500000000000000)
  k := 22
  n := 32
  sFloor := (549755564341/1099511627776)
  nFloor := (885130614711/2361183241434822606848)
  eFloor := (646432356683/2361183241434822606848)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell068
