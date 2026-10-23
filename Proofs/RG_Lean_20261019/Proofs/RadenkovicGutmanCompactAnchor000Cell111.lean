/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell111
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1258109/8589934592)
  b := (1383919/8589934592)
  s := [(2195635372667/2199023255552),(-169000869/549755813888),(-16717263/1099511627776)]
  L := [(20419774259471775493558077/19807040628566084398385987584),(2781358766965/13510798882111488),(23032349741/2251799813685248),(-5434381/844424930131968),(-22133/140737488355328)]
  c := (580364890637/562949953421312)
  R := (-171932224574417/50000000000000)
  total := (-49655338589/1000000000000000)
  k := 10
  n := 32
  sFloor := (2194925934665/4398046511104)
  nFloor := (1403492072311/1152921504606846976)
  eFloor := (1049498599151/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell111
