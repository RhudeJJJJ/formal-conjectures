/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1067127/17179869184)
  b := (1173839/17179869184)
  s := [(4396970081305/4398046511104),(-215205223/4398046511104),(-5370827/2199023255552)]
  L := [(47170783649/281474976710656),(1810893314135/54043195528445952),(45226760645/27021597764222976),(-282799/1688849860263936),(-7043/1688849860263936)]
  c := (47170783649/281474976710656)
  R := (-434701205974023/100000000000000)
  total := (-26700682571/1000000000000000)
  k := 13
  n := 32
  sFloor := (1099186033607/2199023255552)
  nFloor := (1128308368191/4611686018427387904)
  eFloor := (824031015793/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell102
