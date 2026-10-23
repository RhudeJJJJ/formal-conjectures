/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (735163/274877906944)
  b := (808679/274877906944)
  s := [(1099511061607/1099511627776),(-452933/4398046511104),(-11323/2199023255552)]
  L := [(7150952907197841731192730135/20769187434139310514121985316880384),(635129280233/9223372036854775808),(23817200831/6917529027641081856),(-13/18014398509481984),(-1/54043195528445952)]
  c := (396957628279/1152921504606846976)
  R := (-744086772571749/100000000000000)
  total := (-1977111293/1000000000000000)
  k := 22
  n := 32
  sFloor := (137438867839/274877906944)
  nFloor := (958451288413/2361183241434822606848)
  eFloor := (1433414640491/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell069
