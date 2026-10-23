/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (76603/549755813888)
  b := (337053/2199023255552)
  s := [(1099511626239/1099511627776),(-615/2199023255552),(-15/1099511627776)]
  L := [(2484496546018898198739728049/2658455991569831745807614120560689152),(2647994171395/14167099448608935641088),(66199421911/7083549724304467820544),(-25/885443715538058477568),(5/442721857769029238784)]
  c := (275834526999/295147905179352825856)
  R := (-519773532376683/50000000000000)
  total := (-72087553/500000000000000)
  k := 30
  n := 32
  sFloor := (2199023251833/4398046511104)
  nFloor := (666000097995/604462909807314587353088)
  eFloor := (498019201653/604462909807314587353088)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell038
