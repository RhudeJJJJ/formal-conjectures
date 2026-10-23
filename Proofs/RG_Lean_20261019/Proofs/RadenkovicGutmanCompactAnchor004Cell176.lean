/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell176
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1204927/16777216)
  b := (1325419/16777216)
  s := [(6263449889913/35184372088832),(289765689135/35184372088832),(758176003/17592186044416)]
  L := [(2146692821376687178713/2361183241434822606848),(-39369911965/1649267441664),(833347379/3298534883328),(25306847/206158430208),(-2281463/206158430208)]
  c := (1947571438375/2199023255552)
  R := (-303575267117/5000000000000)
  total := (-389087606147/1000000000000000)
  k := 1
  n := 32
  sFloor := (782931236239/8796093022208)
  nFloor := (157742013907/274877906944)
  eFloor := (1937035472043/4398046511104)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell176
