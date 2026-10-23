/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (150567/8796093022208)
  b := (1324989/70368744177664)
  s := [(4398046511087/4398046511104),(-1/4398046511104),(-1/2199023255552)]
  L := [(4685047890471/2417851639229258349412352),(1405507366037/3626777458843887524118528),(35137509103/1813388729421943762059264),(1/56668397794435742564352),(-1/113336795588871485128704)]
  c := (1171261972617/604462909807314587353088)
  R := (-1348476218585197/100000000000000)
  total := (-459991/20000000000000)
  k := 39
  n := 32
  sFloor := (1099511627771/2199023255552)
  nFloor := (136143857661/9671406556917033397649408)
  eFloor := (1040375647827/77371252455336267181195264)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell016
