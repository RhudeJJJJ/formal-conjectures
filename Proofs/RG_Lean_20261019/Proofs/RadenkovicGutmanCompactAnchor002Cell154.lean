/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell154
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (74011/8388608)
  b := (1302593/134217728)
  s := [(1396721169085/4398046511104),(-450536204873/17592186044416),(18453639921/8796093022208)]
  L := [(6690336618518160616783/9444732965739290427392),(88674913415/2199023255552),(-2432809909/824633720832),(47490879/274877906944),(-1591367/206158430208)]
  c := (778857690575/1099511627776)
  R := (-17239651922889/100000000000000)
  total := (-70169989037/500000000000000)
  k := 1
  n := 32
  sFloor := (1293313937827/8796093022208)
  nFloor := (1398349689059/281474976710656)
  eFloor := (1022432273481/281474976710656)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell154
