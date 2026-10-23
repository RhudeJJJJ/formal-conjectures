/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (735163/274877906944)
  b := (808679/274877906944)
  s := [(549755564341/549755813888),(-399275/4398046511104),(-9981/2199023255552)]
  L := [(179145766979/576460752303423488),(429947886865/6917529027641081856),(21497266763/6917529027641081856),(-503/864691128455135232),(-5/432345564227567616)]
  c := (179145766979/576460752303423488)
  R := (-374605450024507/50000000000000)
  total := (-1990815753/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199022047745/4398046511104)
  nFloor := (535504021955/1180591620717411303424)
  eFloor := (782183151681/2361183241434822606848)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell069
