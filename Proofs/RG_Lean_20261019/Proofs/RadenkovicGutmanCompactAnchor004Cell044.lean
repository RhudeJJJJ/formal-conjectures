/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (271413/1099511627776)
  b := (1194217/4398046511104)
  s := [(4398046495463/4398046511104),(-391/549755813888),(-39/1099511627776)]
  L := [(5858322554515/2361183241434822606848),(3514987044553/7083549724304467820544),(87874512937/3541774862152233910272),(-13/442721857769029238784),(-1/221360928884514619392)]
  c := (366145159657/147573952589676412928)
  R := (-990728269735663/100000000000000)
  total := (-243364623/1000000000000000)
  k := 29
  n := 32
  sFloor := (2199023246089/4398046511104)
  nFloor := (1289827329001/302231454903657293676544)
  eFloor := (924368671475/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell044
