/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell122
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (448689/1073741824)
  b := (987115/2147483648)
  s := [(68568406595/68719476736),(-1926957179/4398046511104),(-47391555/2199023255552)]
  L := [(11408657273823047184062375/9903520314283042199192993792),(776322253045/3377699720527872),(4805125445/422212465065984),(-291107/26388279066624),(-14065/52776558133248)]
  c := (648507084055/562949953421312)
  R := (-338313654151963/100000000000000)
  total := (-6967687899/50000000000000)
  k := 10
  n := 32
  sFloor := (2193178140895/4398046511104)
  nFloor := (1209028445637/144115188075855872)
  eFloor := (577441524863/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell122
