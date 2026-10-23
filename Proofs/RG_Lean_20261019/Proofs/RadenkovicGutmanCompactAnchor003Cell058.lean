/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1030685/1099511627776)
  b := (1133753/1099511627776)
  s := [(549755807661/549755813888),(-9963/4398046511104),(-249/2199023255552)]
  L := [(1967388541862973110730167393/332306998946228968225951765070086144),(698953419003/590295810358705651712),(52421249555/885443715538058477568),(-13/36893488147419103232),(1/55340232221128654848)]
  c := (1747392046047/295147905179352825856)
  R := (-118405392157219/12500000000000)
  total := (-883406251/1000000000000000)
  k := 28
  n := 32
  sFloor := (2199023225413/4398046511104)
  nFloor := (865196005877/18889465931478580854784)
  eFloor := (827630108395/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell058
