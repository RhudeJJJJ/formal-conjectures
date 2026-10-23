/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell003
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1395653/281474976710656)
  b := (767609/140737488355328)
  s := [(549755813887/549755813888),(-1/2199023255552)]
  L := [(201345440978687998520918989/170141183460469231731687303715884105728),(3433541590663/14507109835375550096474112),(28612785069/2417851639229258349412352),(11/906694364710971881029632),(-1/151115727451828646838272)]
  c := (715322702329/604462909807314587353088)
  R := (-1373131382724311/100000000000000)
  total := (-3392229/500000000000000)
  k := 40
  n := 32
  sFloor := (2199023255547/4398046511104)
  nFloor := (431785130703/309485009821345068724781056)
  eFloor := (1291515041669/1237940039285380274899124224)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell003
