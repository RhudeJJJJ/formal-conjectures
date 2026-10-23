/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (995649/34359738368)
  b := (1095213/34359738368)
  s := [(4397812178587/4398046511104),(-2928895/274877906944),(-292777/549755813888)]
  L := [(1314281348489/36028797018963968),(1051358345439/144115188075855872),(78833995787/216172782113783808),(-71527/9007199254740992),(-2675/13510798882111488)]
  c := (1314281348489/36028797018963968)
  R := (-510939190083807/100000000000000)
  total := (-14665195993/1000000000000000)
  k := 15
  n := 32
  sFloor := (2198881487025/4398046511104)
  nFloor := (982218269705/18446744073709551616)
  eFloor := (1434675669849/36893488147419103232)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell094
