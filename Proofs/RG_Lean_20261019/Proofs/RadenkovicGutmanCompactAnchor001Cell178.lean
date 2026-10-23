/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell178
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (182245/2097152)
  b := (400939/4194304)
  s := [(5410277418689/17592186044416),(4585702737/1099511627776),(-1993899859/4398046511104)]
  L := [(687621588548366995461/1180591620717411303424),(-8048456867/8796093022208),(2523635963/4398046511104),(12815737/549755813888),(-1695023/274877906944)]
  c := (1279929655481/2199023255552)
  R := (-27060408363167/100000000000000)
  total := (-2350597284939/1000000000000000)
  k := 1
  n := 32
  sFloor := (84535584667/549755813888)
  nFloor := (752783207705/1099511627776)
  eFloor := (684480534157/1099511627776)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell178
