/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell179
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (400939/4194304)
  b := (882065/8388608)
  s := [(1327753029345/4398046511104),(53097235903/17592186044416),(-4263875761/8796093022208)]
  L := [(5618656780354212918731/9444732965739290427392),(9684734063/8796093022208),(2746118659/4398046511104),(-1417721/549755813888),(-1071231/274877906944)]
  c := (81762217165/137438953472)
  R := (-3246028748229/12500000000000)
  total := (-1238117084549/500000000000000)
  k := 1
  n := 32
  sFloor := (1327753029345/8796093022208)
  nFloor := (622289599473/549755813888)
  eFloor := (1121820746589/1099511627776)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell179
