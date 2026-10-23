/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (448689/1073741824)
  b := (987115/2147483648)
  s := [(4343794790943/4398046511104),(-10649762227/4398046511104),(-243451063/2199023255552)]
  L := [(321061018668490748756055/38685626227668133590597632),(1383985821553/844424930131968),(8216258825/105553116266496),(-21016081/52776558133248),(-53957/6597069766656)]
  c := (1168013181699/140737488355328)
  R := (-239579610017267/100000000000000)
  total := (-98117593061/1000000000000000)
  k := 7
  n := 32
  sFloor := (2166329063295/4398046511104)
  nFloor := (1428101121715/144115188075855872)
  eFloor := (533951254911/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell122
