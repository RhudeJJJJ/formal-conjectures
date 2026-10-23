/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell249
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (309211/4096)
  b := (85033/1024)
  s := [(5355920200989/4611686018427387904),(-1584425792143/4611686018427387904),(126495355419/2305843009213693952)]
  L := [(302336751437811796521257/302231454903657293676544),(-152613433/2199023255552),(533653/51539607552),(-184281/137438953472),(1655/12884901888)]
  c := (1099828439195/1099511627776)
  R := (7202420079/50000000000000)
  total := (1195728846253/1000000000000000)
  k := 0
  n := 32
  sFloor := (1006121279921/2305843009213693952)
  nFloor := 2777429331015377192032490018489533744199104636681634713600719832201518931153527929393119232
  eFloor := 2776455570750932233711894991498865953376059998615062375235380785705103012048631909524176896
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell249
