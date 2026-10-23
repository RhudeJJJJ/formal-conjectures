/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell092
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1645703/68719476736)
  b := (56571/2147483648)
  s := [(4398013998773/4398046511104),(-6502337/4398046511104),(-162549/2199023255552)]
  L := [(1253942565482516274735726747/324518553658426726783156020576256),(1336448290441/1729382256910270464),(11136620315/288230376151711744),(-6761/54043195528445952),(-57/18014398509481984)]
  c := (278431181551/72057594037927936)
  R := (-623190267476227/100000000000000)
  total := (-3702050719/250000000000000)
  k := 18
  n := 32
  sFloor := (2199003585669/4398046511104)
  nFloor := (1102898506009/36893488147419103232)
  eFloor := (131876476395/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell092
