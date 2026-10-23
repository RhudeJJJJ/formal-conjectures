/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell175
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1095389/16777216)
  b := (1204927/16777216)
  s := [(5195466296939/17592186044416),(68578900549/17592186044416),(197011497/8796093022208)]
  L := [(1387001961382812728945/2361183241434822606848),(-8268619533/4398046511104),(-211422611/2199023255552),(25408817/274877906944),(-1352869/137438953472)]
  c := (643791064963/1099511627776)
  R := (-26762357263709/100000000000000)
  total := (-1742057168209/1000000000000000)
  k := 1
  n := 32
  sFloor := (649433287117/4398046511104)
  nFloor := (656185739823/2199023255552)
  eFloor := (607696311991/2199023255552)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell175
