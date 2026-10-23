/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1407947/2199023255552)
  b := (1548741/2199023255552)
  s := [(1099511599173/1099511627776),(-11441/2199023255552),(-143/549755813888)]
  L := [(1314141308625/73786976294838206464),(3153923376169/885443715538058477568),(78847684067/442721857769029238784),(-115/55340232221128654848),(1/27670116110564327424)]
  c := (1314141308625/73786976294838206464)
  R := (-892175467296851/100000000000000)
  total := (-568122347/1000000000000000)
  k := 26
  n := 32
  sFloor := (2199023186333/4398046511104)
  nFloor := (491030056161/18889465931478580854784)
  eFloor := (1434444639491/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell054
