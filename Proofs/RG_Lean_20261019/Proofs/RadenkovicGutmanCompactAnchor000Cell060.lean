/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (155891/137438953472)
  b := (21435/17179869184)
  s := [(4398046103779/4398046511104),(-40733/2199023255552),(-509/549755813888)]
  L := [(643085775903104162504260247/10384593717069655257060992658440192),(456936952263/36893488147419103232),(34270038713/55340232221128654848),(-29/1152921504606846976),(1/3458764513820540928)]
  c := (571174908173/9223372036854775808)
  R := (-829865552826911/100000000000000)
  total := (-935783761/1000000000000000)
  k := 24
  n := 32
  sFloor := (68719469035/137438953472)
  nFloor := (1379097041773/18889465931478580854784)
  eFloor := (1031256316363/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell060
