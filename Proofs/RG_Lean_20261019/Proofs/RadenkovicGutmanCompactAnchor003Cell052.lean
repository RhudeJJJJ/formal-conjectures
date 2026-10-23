/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1163593/2199023255552)
  b := (79997/137438953472)
  s := [(4398046495231/4398046511104),(-1587/2199023255552),(-5/137438953472)]
  L := [(1113552381733/590295810358705651712),(2672518815211/7083549724304467820544),(66812797103/3541774862152233910272),(-19/442721857769029238784),(1/221360928884514619392)]
  c := (1113552381733/590295810358705651712)
  R := (-502214477342009/50000000000000)
  total := (-264460823/500000000000000)
  k := 29
  n := 32
  sFloor := (549755811487/1099511627776)
  nFloor := (1102718839747/75557863725914323419136)
  eFloor := (131854993937/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell052
