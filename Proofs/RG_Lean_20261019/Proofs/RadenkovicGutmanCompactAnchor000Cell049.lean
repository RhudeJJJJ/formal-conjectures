/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (874225/2199023255552)
  b := (1923295/4398046511104)
  s := [(4398046461065/4398046511104),(-1251/549755813888),(-125/1099511627776)]
  L := [(79001135216402887882343319/10384593717069655257060992658440192),(1347208370287/885443715538058477568),(33680207609/442721857769029238784),(-1/55340232221128654848),(-5/27670116110564327424)]
  c := (70167103431/9223372036854775808)
  R := (-233676586865317/25000000000000)
  total := (-92417379/250000000000000)
  k := 27
  n := 32
  sFloor := (1099511612639/2199023255552)
  nFloor := (677671482901/75557863725914323419136)
  eFloor := (63343348581/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell049
