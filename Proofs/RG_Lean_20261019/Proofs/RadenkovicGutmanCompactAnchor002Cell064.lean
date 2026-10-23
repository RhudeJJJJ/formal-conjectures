/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (912959/549755813888)
  b := (502127/274877906944)
  s := [(2199022870705/2199023255552),(-76969/2199023255552),(-481/274877906944)]
  L := [(2210201795289/18446744073709551616),(1326107767117/55340232221128654848),(4144042955/3458764513820540928),(-295/3458764513820540928),(-1/432345564227567616)]
  c := (276275224411/2305843009213693952)
  R := (-796865730923087/100000000000000)
  total := (-1315273701/1000000000000000)
  k := 23
  n := 32
  sFloor := (8589932773/17179869184)
  nFloor := (412921985613/2361183241434822606848)
  eFloor := (1206267765851/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell064
