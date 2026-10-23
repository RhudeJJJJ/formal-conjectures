/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1395883/137438953472)
  b := (1535471/137438953472)
  s := [(4398040779531/4398046511104),(-1146311/4398046511104),(-28657/2199023255552)]
  L := [(786469515747/1152921504606846976),(314586679879/2305843009213693952),(7864605063/1152921504606846976),(-563/144115188075855872),(-7/72057594037927936)]
  c := (786469515747/1152921504606846976)
  R := (-354950275857099/50000000000000)
  total := (-1432169047/200000000000000)
  k := 21
  n := 32
  sFloor := (2199019787953/4398046511104)
  nFloor := (365667632451/73786976294838206464)
  eFloor := (174646007815/36893488147419103232)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell083
