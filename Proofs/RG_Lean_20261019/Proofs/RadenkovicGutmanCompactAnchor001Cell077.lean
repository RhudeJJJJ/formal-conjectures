/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell077
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1575883/274877906944)
  b := (866735/137438953472)
  s := [(1099511171209/1099511627776),(-91313/1099511627776),(-4565/1099511627776)]
  L := [(4009518423317/18446744073709551616),(2405690111189/55340232221128654848),(60141646937/27670116110564327424),(-1373/3458764513820540928),(-17/1729382256910270464)]
  c := (1002379605829/4611686018427387904)
  R := (-1227338183979/160000000000)
  total := (-2184970543/500000000000000)
  k := 23
  n := 32
  sFloor := (1099511075331/2199023255552)
  nFloor := (466054195351/295147905179352825856)
  eFloor := (890365976851/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell077
