/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (987115/2147483648)
  b := (542913/1073741824)
  s := [(4386120298037/4398046511104),(-2375019715/4398046511104),(-58189077/2199023255552)]
  L := [(3514072206158316096275477/2475880078570760549798248448),(1911910723795/6755399441055744),(23614907297/1688849860263936),(-7046377/422212465065984),(-42215/105553116266496)]
  c := (799007513287/562949953421312)
  R := (-65575756614059/20000000000000)
  total := (-74247214701/500000000000000)
  k := 10
  n := 32
  sFloor := (547953612521/1099511627776)
  nFloor := (793612229705/72057594037927936)
  eFloor := (189788229529/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell123
