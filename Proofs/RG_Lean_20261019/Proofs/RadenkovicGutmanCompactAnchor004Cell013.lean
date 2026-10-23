/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (904987/70368744177664)
  b := (995485/70368744177664)
  s := [(4398046511061/4398046511104),(-7/4398046511104),(-1/2199023255552)]
  L := [(17903440909275984743765923/2658455991569831745807614120560689152),(2442443805329/1813388729421943762059264),(61060622741/906694364710971881029632),(19/113336795588871485128704),(-5/56668397794435742564352)]
  c := (2035385581311/302231454903657293676544)
  R := (-1286188684597751/100000000000000)
  total := (-4119707/250000000000000)
  k := 38
  n := 32
  sFloor := (1099511627763/2199023255552)
  nFloor := (896261997817/77371252455336267181195264)
  eFloor := (160578957661/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell013
