/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (837135/8796093022208)
  b := (1841697/17592186044416)
  s := [(2199023255295/2199023255552),(-13/549755813888),(-1/1099511627776)]
  L := [(576367458379/9444732965739290427392),(922187933289/75557863725914323419136),(69164094949/113336795588871485128704),(1/4722366482869645213696),(-1/7083549724304467820544)]
  c := (576367458379/9444732965739290427392)
  R := (-73499165431443/6250000000000)
  total := (-111459409/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255241/4398046511104)
  nFloor := (1141520170845/2417851639229258349412352)
  eFloor := (1091956569751/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell034
