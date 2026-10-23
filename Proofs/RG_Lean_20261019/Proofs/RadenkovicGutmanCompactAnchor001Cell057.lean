/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (936987/1099511627776)
  b := (1030685/1099511627776)
  s := [(137438952211/137438953472),(-4035/2199023255552),(-101/1099511627776)]
  L := [(398980241308544194199524795/83076749736557242056487941267521536),(212617793557/221360928884514619392),(1328851231/27670116110564327424),(-19/55340232221128654848),(1/13835058055282163712)]
  c := (1417462560867/295147905179352825856)
  R := (-478852970449089/50000000000000)
  total := (-812011219/1000000000000000)
  k := 28
  n := 32
  sFloor := (2199023231139/4398046511104)
  nFloor := (659045807327/18889465931478580854784)
  eFloor := (629531897841/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell057
