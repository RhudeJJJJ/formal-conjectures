/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (936987/1099511627776)
  b := (1030685/1099511627776)
  s := [(2199023234967/2199023255552),(-4117/2199023255552),(-103/1099511627776)]
  L := [(406485788934737705013301717/83076749736557242056487941267521536),(1732940182891/1770887431076116955136),(43323179051/885443715538058477568),(-1/27670116110564327424),(-5/55340232221128654848)]
  c := (722063811293/147573952589676412928)
  R := (-956774087214513/100000000000000)
  total := (-811217113/1000000000000000)
  k := 28
  n := 32
  sFloor := (549755807661/1099511627776)
  nFloor := (715038992625/18889465931478580854784)
  eFloor := (1367985508379/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell057
