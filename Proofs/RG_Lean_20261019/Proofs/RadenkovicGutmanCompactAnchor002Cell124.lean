/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (542913/1073741824)
  b := (149301/268435456)
  s := [(4328407281287/4398046511104),(-27194332987/8796093022208),(-605290229/4398046511104)]
  L := [(52839466626054341495057/4835703278458516698824704),(3631062100751/1688849860263936),(28308124061/281474976710656),(-70273781/105553116266496),(-225857/17592186044416)]
  c := (384457719527/35184372088832)
  R := (-22582617337851/10000000000000)
  total := (-55888927051/500000000000000)
  k := 7
  n := 32
  sFloor := (1078551206141/2199023255552)
  nFloor := (1168221221961/72057594037927936)
  eFloor := (1706367113053/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell124
