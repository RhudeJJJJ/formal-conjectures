/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell032
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1383695/17592186044416)
  b := (95129/1099511627776)
  s := [(4398046510753/4398046511104),(-35/2199023255552),(-1/1099511627776)]
  L := [(787334352131/18889465931478580854784),(1889595616835/226673591177742970257408),(47239719731/113336795588871485128704),(-5/14167099448608935641088),(1/7083549724304467820544)]
  c := (787334352131/18889465931478580854784)
  R := (-1493810782651/125000000000)
  total := (-93614229/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255339/4398046511104)
  nFloor := (779674521049/2417851639229258349412352)
  eFloor := (745821876189/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell032
