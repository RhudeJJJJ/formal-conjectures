/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (995485/70368744177664)
  b := (1095033/70368744177664)
  s := [(68719476735/68719476736),(-11/4398046511104),(-1/2199023255552)]
  L := [(5822862370281/604462909807314587353088),(3493699874291/1813388729421943762059264),(87342058187/906694364710971881029632),(-5/113336795588871485128704),(1/56668397794435742564352)]
  c := (727857796285/75557863725914323419136)
  R := (-1268290709563321/100000000000000)
  total := (-17873551/1000000000000000)
  k := 37
  n := 32
  sFloor := (2199023255513/4398046511104)
  nFloor := (878703199781/77371252455336267181195264)
  eFloor := (1314147152117/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell014
