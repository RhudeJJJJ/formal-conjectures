/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1104679/549755813888)
  b := (607573/274877906944)
  s := [(2199022737363/2199023255552),(-207271/4398046511104),(-5183/2199023255552)]
  L := [(106704788338150262068051897/649037107316853453566312041152512),(1819624229549/55340232221128654848),(45490191155/27670116110564327424),(-533/3458764513820540928),(-11/1729382256910270464)]
  c := (1516366244489/9223372036854775808)
  R := (-390523360380763/50000000000000)
  total := (-194961929/125000000000000)
  k := 23
  n := 32
  sFloor := (34359728571/68719476736)
  nFloor := (667717105079/2361183241434822606848)
  eFloor := (1914106669977/9444732965739290427392)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell066
