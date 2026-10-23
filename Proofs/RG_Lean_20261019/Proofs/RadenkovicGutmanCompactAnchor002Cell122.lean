/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (448689/1073741824)
  b := (987115/2147483648)
  s := [(1087529371725/1099511627776),(-9428907231/4398046511104),(-217836805/2199023255552)]
  L := [(72552845926689555789303/9671406556917033397649408),(626410912093/422212465065984),(2494090717/35184372088832),(-8459605/26388279066624),(-7419/1099511627776)]
  c := (2111565727003/281474976710656)
  R := (-122315345698301/50000000000000)
  total := (-100225201501/1000000000000000)
  k := 8
  n := 32
  sFloor := (2170126453029/4398046511104)
  nFloor := (199476876145/18014398509481984)
  eFloor := (18210397687/2251799813685248)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell122
