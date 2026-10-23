/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (748047/34359738368)
  b := (1645703/68719476736)
  s := [(4397896454813/4398046511104),(-30009639/4398046511104),(-750059/2199023255552)]
  L := [(925442733798083943666897201/40564819207303340847894502572032),(986312993015/216172782113783808),(8218110089/36028797018963968),(-1339/422212465065984),(-179/2251799813685248)]
  c := (1643916529655/72057594037927936)
  R := (-267203486819983/50000000000000)
  total := (-5764589921/500000000000000)
  k := 16
  n := 32
  sFloor := (137433279533/274877906944)
  nFloor := (992340115943/36893488147419103232)
  eFloor := (1484097183861/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell091
