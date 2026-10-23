/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (602367/17179869184)
  b := (1325207/34359738368)
  s := [(4397703438507/4398046511104),(-34303117/2199023255552),(-53569/68719476736)]
  L := [(481046648691/9007199254740992),(36075503825/3377699720527872),(450798563/844424930131968),(-28741/1688849860263936),(-359/844424930131968)]
  c := (481046648691/9007199254740992)
  R := (-245939262115047/50000000000000)
  total := (-17076663291/1000000000000000)
  k := 15
  n := 32
  sFloor := (274851962741/549755813888)
  nFloor := (719031367621/9223372036854775808)
  eFloor := (525126057423/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell096
