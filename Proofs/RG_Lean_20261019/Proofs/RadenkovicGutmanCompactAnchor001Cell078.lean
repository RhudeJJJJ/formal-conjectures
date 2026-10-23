/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell078
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (866735/137438953472)
  b := (1906817/274877906944)
  s := [(1099511075331/1099511627776),(-220979/2199023255552),(-1381/274877906944)]
  L := [(2425754775417/9223372036854775808),(1455452061971/27670116110564327424),(12128740435/4611686018427387904),(-1019/1729382256910270464),(-3/288230376151711744)]
  c := (303219346927/1152921504606846976)
  R := (-757555426789591/100000000000000)
  total := (-4746865789/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199021918635/4398046511104)
  nFloor := (1127849461849/590295810358705651712)
  eFloor := (1077341216749/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell078
