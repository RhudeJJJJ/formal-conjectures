/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1548741/2199023255552)
  b := (851807/1099511627776)
  s := [(549755810373/549755813888),(-5623/4398046511104),(-141/2199023255552)]
  L := [(555272075039896548442597523/166153499473114484112975882535043072),(1578166937045/2361183241434822606848),(118361676151/3541774862152233910272),(-5/147573952589676412928),(-7/221360928884514619392)]
  c := (986361348225/295147905179352825856)
  R := (-975835983736711/100000000000000)
  total := (-27354139/40000000000000)
  k := 29
  n := 32
  sFloor := (2199023238539/4398046511104)
  nFloor := (976765226919/37778931862957161709568)
  eFloor := (934355111609/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell055
