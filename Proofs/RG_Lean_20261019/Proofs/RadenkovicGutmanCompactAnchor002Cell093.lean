/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (56571/2147483648)
  b := (995649/34359738368)
  s := [(4397852844909/4398046511104),(-19365207/2199023255552),(-483977/1099511627776)]
  L := [(543097251297/18014398509481984),(162920766095/27021597764222976),(32578074217/108086391056891904),(-9161/1688849860263936),(-913/6755399441055744)]
  c := (543097251297/18014398509481984)
  R := (-32529354716871/6250000000000)
  total := (-679154707/50000000000000)
  k := 16
  n := 32
  sFloor := (2198906089293/4398046511104)
  nFloor := (405875802357/9223372036854775808)
  eFloor := (1185683783967/36893488147419103232)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell093
