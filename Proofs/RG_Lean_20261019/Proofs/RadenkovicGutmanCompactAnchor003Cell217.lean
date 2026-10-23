/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell217
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (468645/131072)
  b := (1031019/262144)
  s := [(4686238759695/562949953421312),(-586811144485/281474976710656),(19886270743/70368744177664)]
  L := [(2604234451378270923151/2361183241434822606848),(-91458496609/6597069766656),(3666133883/3298534883328),(-2069383/51539607552),(-558377/206158430208)]
  c := (1198623004091/1099511627776)
  R := (4315364742777/100000000000000)
  total := (1644610444541/100000000000000)
  k := 0
  n := 32
  sFloor := (917926659167/281474976710656)
  nFloor := 305718265438456829223693713408
  eFloor := 272609082351706524498222120960
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell217
