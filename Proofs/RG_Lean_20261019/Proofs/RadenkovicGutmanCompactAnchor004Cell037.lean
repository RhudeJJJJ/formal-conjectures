/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (557113/4398046511104)
  b := (76603/549755813888)
  s := [(4398046506985/4398046511104),(-823/4398046511104),(-21/2199023255552)]
  L := [(6170758984197/9444732965739290427392),(154268143733/1180591620717411303424),(46280193743/7083549724304467820544),(-1/147573952589676412928),(1/442721857769029238784)]
  c := (1542689746049/2361183241434822606848)
  R := (-16522579080133/1562500000000)
  total := (-133335669/1000000000000000)
  k := 31
  n := 32
  sFloor := (549755813265/1099511627776)
  nFloor := (679308239095/604462909807314587353088)
  eFloor := (1947334314835/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell037
