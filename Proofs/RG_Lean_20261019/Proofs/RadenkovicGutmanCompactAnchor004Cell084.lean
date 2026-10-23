/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1535471/137438953472)
  b := (844509/68719476736)
  s := [(4398014474671/4398046511104),(-1601803/1099511627776),(-40043/549755813888)]
  L := [(51538505897803672988281313/10141204801825835211973625643008),(3515521348687/3458764513820540928),(87885354755/1729382256910270464),(-32731/216172782113783808),(-419/108086391056891904)]
  c := (22887694361/4503599627370496)
  R := (-121897881501909/20000000000000)
  total := (-1351029103/200000000000000)
  k := 18
  n := 32
  sFloor := (2199003873557/4398046511104)
  nFloor := (80627568857/9223372036854775808)
  eFloor := (1849043752369/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell084
