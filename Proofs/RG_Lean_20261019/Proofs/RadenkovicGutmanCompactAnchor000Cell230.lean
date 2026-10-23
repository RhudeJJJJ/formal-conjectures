/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell230
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (404471/32768)
  b := (222459/16384)
  s := [(4664719721399/18014398509481984),(-2714870948865/36028797018963968),(213268858997/18014398509481984)]
  L := [(19121699899452347431445/18889465931478580854784),(-30975736487/13194139533312),(2194552115/6597069766656),(-33493573/824633720832),(1520029/412316860416)]
  c := (1110773266461/1099511627776)
  R := (509515138389/100000000000000)
  total := (1721805207941/250000000000000)
  k := 0
  n := 32
  sFloor := (1760276552981/18014398509481984)
  nFloor := 2807085018795406422190248119226678505679511093248
  eFloor := 2771557103910459642645172694934055310118797443072
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell230
