/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell036
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1012933/8796093022208)
  b := (557113/4398046511104)
  s := [(1099511626925/1099511627776),(-681/4398046511104),(-17/2199023255552)]
  L := [(5099803560429/9444732965739290427392),(254989422613/2361183241434822606848),(38248300019/7083549724304467820544),(-1/147573952589676412928),(1/442721857769029238784)]
  c := (1274950890107/2361183241434822606848)
  R := (-1066976052176107/100000000000000)
  total := (-1911127/15625000000000)
  k := 31
  n := 32
  sFloor := (549755813373/1099511627776)
  nFloor := (1122824140323/1208925819614629174706176)
  eFloor := (1609368068971/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell036
