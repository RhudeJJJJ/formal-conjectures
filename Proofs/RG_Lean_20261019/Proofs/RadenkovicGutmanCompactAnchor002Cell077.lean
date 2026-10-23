/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell077
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1575883/274877906944)
  b := (866735/137438953472)
  s := [(4398037337883/4398046511104),(-14333/34359738368),(-5733/274877906944)]
  L := [(1646328440871/1152921504606846976),(658524540741/2305843009213693952),(49388512205/3458764513820540928),(-1755/144115188075855872),(-65/216172782113783808)]
  c := (1646328440871/1152921504606846976)
  R := (-336481552412869/50000000000000)
  total := (-3830334211/1000000000000000)
  k := 20
  n := 32
  sFloor := (2199017705765/4398046511104)
  nFloor := (1230306732847/590295810358705651712)
  eFloor := (1797045696669/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell077
