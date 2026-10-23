/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1095213/34359738368)
  b := (602367/17179869184)
  s := [(4397785749487/4398046511104),(-26073759/2199023255552),(-325785/549755813888)]
  L := [(104877574749837423552620363/2535301200456458802993406410752),(3576733038037/432345564227567616),(29798790531/72057594037927936),(-271309/27021597764222976),(-1131/4503599627370496)]
  c := (372599994413/9007199254740992)
  R := (-126162866119473/25000000000000)
  total := (-1991423003/125000000000000)
  k := 15
  n := 32
  sFloor := (549716374461/1099511627776)
  nFloor := (1312645709817/18446744073709551616)
  eFloor := (940721728421/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell095
