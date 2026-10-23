/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell184
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1291429/8388608)
  b := (1420571/8388608)
  s := [(4252753310067/17592186044416),(141104224857/17592186044416),(-9345579983/8796093022208)]
  L := [(3542779596588744338717/4722366482869645213696),(-126135847185/8796093022208),(37444739845/13194139533312),(-81833013/549755813888),(1298615/824633720832)]
  c := (812059133347/1099511627776)
  R := (-3788102795279/25000000000000)
  total := (-1138413085961/500000000000000)
  k := 1
  n := 32
  sFloor := (2126376655033/17592186044416)
  nFloor := (1016365524365/137438953472)
  eFloor := (413639494905/68719476736)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell184
