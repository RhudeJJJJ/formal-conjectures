/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell101
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (242529/4294967296)
  b := (1067127/17179869184)
  s := [(4397156841211/4398046511104),(-88939345/2199023255552),(-138769/68719476736)]
  L := [(4990189353243/36028797018963968),(2993476357489/108086391056891904),(74774588695/54043195528445952),(-772825/6755399441055744),(-9631/3377699720527872)]
  c := (623773669155/4503599627370496)
  R := (-88845999592839/20000000000000)
  total := (-4962285607/200000000000000)
  k := 13
  n := 32
  sFloor := (549621260163/1099511627776)
  nFloor := (1864974503523/9223372036854775808)
  eFloor := (340509044889/2305843009213693952)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell101
