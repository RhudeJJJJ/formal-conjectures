/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell019
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1603235/70368744177664)
  b := (881779/35184372088832)
  s := [(4398046510959/4398046511104),(-29/4398046511104),(-1/2199023255552)]
  L := [(3407954841833/151115727451828646838272),(2044766527975/453347182355485940514816),(17039667947/75557863725914323419136),(-13/28334198897217871282176),(1/4722366482869645213696)]
  c := (425994355229/18889465931478580854784)
  R := (-612879985723603/50000000000000)
  total := (-13908267/500000000000000)
  k := 36
  n := 32
  sFloor := (274877906933/549755813888)
  nFloor := (159173161395/4835703278458516698824704)
  eFloor := (232496040973/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell019
