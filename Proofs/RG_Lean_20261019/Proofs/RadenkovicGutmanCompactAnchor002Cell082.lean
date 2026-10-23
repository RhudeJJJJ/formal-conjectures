/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell082
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1268985/137438953472)
  b := (1395883/137438953472)
  s := [(4398022718353/4398046511104),(-1189623/1099511627776),(-59479/1099511627776)]
  L := [(2135059771575/576460752303423488),(2562047471521/3458764513820540928),(64049518517/1729382256910270464),(-17701/216172782113783808),(-221/108086391056891904)]
  c := (2135059771575/576460752303423488)
  R := (-625308394738283/100000000000000)
  total := (-1432201771/250000000000000)
  k := 19
  n := 32
  sFloor := (549752215243/1099511627776)
  nFloor := (1595542710833/295147905179352825856)
  eFloor := (582631771421/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell082
