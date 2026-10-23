/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (904987/70368744177664)
  b := (995485/70368744177664)
  s := [(4398046511057/4398046511104),(-7/4398046511104),(-1/2199023255552)]
  L := [(1222598687751132894708731311/170141183460469231731687303715884105728),(1303052845393/906694364710971881029632),(32576069177/453347182355485940514816),(-1/14167099448608935641088),(1/28334198897217871282176)]
  c := (542942885207/75557863725914323419136)
  R := (-320736446937357/25000000000000)
  total := (-16437123/1000000000000000)
  k := 38
  n := 32
  sFloor := (549755813881/1099511627776)
  nFloor := (811484325391/77371252455336267181195264)
  eFloor := (74080835657/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell013
