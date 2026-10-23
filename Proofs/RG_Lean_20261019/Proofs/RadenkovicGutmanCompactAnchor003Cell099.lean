/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1603499/34359738368)
  b := (220481/4294967296)
  s := [(4397923050551/4398046511104),(-24690875/4398046511104),(-617141/2199023255552)]
  L := [(37200801112623505349413153/2535301200456458802993406410752),(1268726290727/432345564227567616),(31714077509/216172782113783808),(-48785/27021597764222976),(-605/13510798882111488)]
  c := (1057310359801/72057594037927936)
  R := (-556474635418241/100000000000000)
  total := (-6435874939/250000000000000)
  k := 17
  n := 32
  sFloor := (2198948562697/4398046511104)
  nFloor := (130882054753/1152921504606846976)
  eFloor := (7824955719/72057594037927936)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell099
