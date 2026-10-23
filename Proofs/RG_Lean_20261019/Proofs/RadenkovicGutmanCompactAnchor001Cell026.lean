/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (781061/17592186044416)
  b := (859167/17592186044416)
  s := [(2199023255497/2199023255552),(-21/4398046511104),(-1/2199023255552)]
  L := [(1108955603590922571184736009/85070591730234615865843651857942052864),(2363878018661/906694364710971881029632),(59096874859/453347182355485940514816),(-17/56668397794435742564352),(5/28334198897217871282176)]
  c := (1969900871029/151115727451828646838272)
  R := (-1253166428248901/100000000000000)
  total := (-1385583/25000000000000)
  k := 37
  n := 32
  sFloor := (2199023255485/4398046511104)
  nFloor := (228975165307/2417851639229258349412352)
  eFloor := (874884074961/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell026
