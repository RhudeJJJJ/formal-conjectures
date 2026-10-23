/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (538175/137438953472)
  b := (1183985/274877906944)
  s := [(1099510557929/1099511627776),(-427939/2199023255552),(-5349/549755813888)]
  L := [(1729441366199932941317701023/2596148429267413814265248164610048),(1228840778195/9223372036854775808),(92162691931/13835058055282163712),(-1529/576460752303423488),(-55/864691128455135232)]
  c := (1536052499595/2305843009213693952)
  R := (-355543527116573/50000000000000)
  total := (-2765476347/1000000000000000)
  k := 21
  n := 32
  sFloor := (2199020666523/4398046511104)
  nFloor := (1147895847745/1180591620717411303424)
  eFloor := (104792022479/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell073
