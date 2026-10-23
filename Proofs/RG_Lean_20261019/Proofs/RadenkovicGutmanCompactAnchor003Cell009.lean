/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1236239/140737488355328)
  b := (679931/70368744177664)
  s := [(4398046511099/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(5027745950797/9671406556917033397649408),(1005541869599/9671406556917033397649408),(75415091309/14507109835375550096474112),(-9/604462909807314587353088),(7/906694364710971881029632)]
  c := (1256936487699/2417851639229258349412352)
  R := (-1414261155399283/100000000000000)
  total := (-1238027/100000000000000)
  k := 41
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (311176995929/77371252455336267181195264)
  eFloor := (74416504793/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell009
