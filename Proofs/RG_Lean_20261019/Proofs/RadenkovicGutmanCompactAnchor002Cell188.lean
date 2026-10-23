/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell188
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1890779/8388608)
  b := (129991/524288)
  s := [(4553512285181/17592186044416),(3967294433/17592186044416),(-9408057231/8796093022208)]
  L := [(3452422413511430501001/4722366482869645213696),(135012173621/26388279066624),(11002875737/4398046511104),(-430528775/1649267441664),(4184835/274877906944)]
  c := (1607659465405/2199023255552)
  R := (-7830847848641/50000000000000)
  total := (-5435839891/1562500000000)
  k := 1
  n := 32
  sFloor := (70916616643/549755813888)
  nFloor := (1036249044533/17179869184)
  eFloor := (1669067639677/34359738368)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell188
