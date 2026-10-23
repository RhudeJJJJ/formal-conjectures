/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (56571/2147483648)
  b := (995649/34359738368)
  s := [(4398007952769/4398046511104),(-1927877/1099511627776),(-96387/1099511627776)]
  L := [(5290880544749/1152921504606846976),(3174476713325/3458764513820540928),(26452778271/576460752303423488),(-38213/216172782113783808),(-159/36028797018963968)]
  c := (1322720136187/288230376151711744)
  R := (-614591251553313/100000000000000)
  total := (-8031255243/500000000000000)
  k := 18
  n := 32
  sFloor := (137437495491/274877906944)
  nFloor := (1230003003365/36893488147419103232)
  eFloor := (73432501945/2305843009213693952)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell093
