/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (586823/17592186044416)
  b := (645505/17592186044416)
  s := [(4398046510751/4398046511104),(-35/2199023255552),(-1/1099511627776)]
  L := [(4046796209321/75557863725914323419136),(809355104131/75557863725914323419136),(60701322457/113336795588871485128704),(1/4722366482869645213696),(-1/7083549724304467820544)]
  c := (505849526165/9444732965739290427392)
  R := (-147813994362429/12500000000000)
  total := (-39283413/1000000000000000)
  k := 35
  n := 32
  sFloor := (1099511627669/2199023255552)
  nFloor := (1221369337657/19342813113834066795298816)
  eFloor := (114163906337/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell023
