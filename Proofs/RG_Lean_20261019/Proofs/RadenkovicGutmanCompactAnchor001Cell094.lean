/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (995649/34359738368)
  b := (1095213/34359738368)
  s := [(4397999855713/4398046511104),(-4665419/2199023255552),(-116625/1099511627776)]
  L := [(900993631296983582482626041/162259276829213363391578010288128),(1280362466439/1152921504606846976),(96021841279/1729382256910270464),(-18643/72057594037927936),(-703/108086391056891904)]
  c := (800243099605/144115188075855872)
  R := (-605060394947841/100000000000000)
  total := (-17392533887/1000000000000000)
  k := 18
  n := 32
  sFloor := (2198995029187/4398046511104)
  nFloor := (744150930471/18446744073709551616)
  eFloor := (710825771077/18446744073709551616)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell094
