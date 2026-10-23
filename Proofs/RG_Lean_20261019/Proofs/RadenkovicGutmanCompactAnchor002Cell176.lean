/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell176
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1204927/16777216)
  b := (1325419/16777216)
  s := [(1486923489195/8796093022208),(137193636051/17592186044416),(652100915/8796093022208)]
  L := [(2173486247582720037031/2361183241434822606848),(-192989439441/8796093022208),(1169769131/13194139533312),(64046373/549755813888),(-8034299/824633720832)]
  c := (988199585173/1099511627776)
  R := (-5336834941013/100000000000000)
  total := (-170176525533/500000000000000)
  k := 1
  n := 32
  sFloor := (1486923489195/17592186044416)
  nFloor := (1076525381683/2199023255552)
  eFloor := (207818678547/549755813888)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell176
