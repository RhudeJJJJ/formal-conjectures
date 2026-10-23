/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (264453/549755813888)
  b := (1163593/2199023255552)
  s := [(2199023249123/2199023255552),(-643/1099511627776),(-1/34359738368)]
  L := [(451649419585/295147905179352825856),(2167913108183/7083549724304467820544),(54197724517/3541774862152233910272),(-5/442721857769029238784),(-1/221360928884514619392)]
  c := (451649419585/295147905179352825856)
  R := (-1014891809131697/100000000000000)
  total := (-121467821/250000000000000)
  k := 30
  n := 32
  sFloor := (2199023247773/4398046511104)
  nFloor := (839973238147/75557863725914323419136)
  eFloor := (802356893663/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell051
