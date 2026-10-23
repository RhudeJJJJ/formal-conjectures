/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell229
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (367701/32768)
  b := (404471/32768)
  s := [(1543765292315/4503599627370496),(-1790728366871/18014398509481984),(140193459505/9007199254740992)]
  L := [(2395984000016334461867/2361183241434822606848),(-1535583329/549755813888),(1292787629/3298534883328),(-6499871/137438953472),(874921/206158430208)]
  c := (1113029423645/1099511627776)
  R := (610970090671/100000000000000)
  total := (3751204175839/500000000000000)
  k := 0
  n := 32
  sFloor := (1166179930349/9007199254740992)
  nFloor := 12032017276828896453308842460445744129029288899869933568
  eFloor := 11849130582836134551768396164557419092969063083805769728
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell229
