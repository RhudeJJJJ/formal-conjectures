/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (205679/17592186044416)
  b := (904987/70368744177664)
  s := [(549755813887/549755813888),(-1/2199023255552)]
  L := [(1230393818134756199554654589/1361129467683753853853498429727072845824),(2622723041281/14507109835375550096474112),(21855866013/2417851639229258349412352),(-37/906694364710971881029632),(3/151115727451828646838272)]
  c := (2185618473999/2417851639229258349412352)
  R := (-693300041661751/50000000000000)
  total := (-100967/6250000000000)
  k := 41
  n := 32
  sFloor := (2199023255547/4398046511104)
  nFloor := (1016198040681/154742504910672534362390528)
  eFloor := (485344929005/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell012
