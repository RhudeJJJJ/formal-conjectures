/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (337053/2199023255552)
  b := (1483033/8796093022208)
  s := [(2199023251833/2199023255552),(-745/2199023255552),(-9/549755813888)]
  L := [(2670075051823/2361183241434822606848),(1602042651781/7083549724304467820544),(40051006619/3541774862152233910272),(-7/442721857769029238784),(1/221360928884514619392)]
  c := (1335037525911/1180591620717411303424)
  R := (-1030016106125693/100000000000000)
  total := (-157132473/1000000000000000)
  k := 30
  n := 32
  sFloor := (549755812763/1099511627776)
  nFloor := (805859162215/604462909807314587353088)
  eFloor := (1205205037715/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell039
