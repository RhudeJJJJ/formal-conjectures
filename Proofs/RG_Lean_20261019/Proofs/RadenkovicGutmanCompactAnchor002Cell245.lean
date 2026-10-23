/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell245
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (422391/8192)
  b := (232315/4096)
  s := [(8397692212615/2305843009213693952),(-2482957739435/2305843009213693952),(198128696505/1152921504606846976)]
  L := [(9451759456586480131151/9444732965739290427392),(-975403855/6597069766656),(72576121/3298534883328),(-1171619/412316860416),(55991/206158430208)]
  c := (1100188418001/1099511627776)
  R := (3845923491/12500000000000)
  total := (1744009128893/1000000000000000)
  k := 0
  n := 32
  sFloor := (1577747966547/1152921504606846976)
  nFloor := 31655233820260412137409643739809693721074127014532823837924147204756743449313542144
  eFloor := 31631470739228406205383535412408084040991935398121053134336851411719959600569516032
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell245
