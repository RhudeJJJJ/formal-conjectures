/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (264453/549755813888)
  b := (1163593/2199023255552)
  s := [(4398046446521/4398046511104),(-6457/2199023255552),(-81/549755813888)]
  L := [(1483598662383/147573952589676412928),(593438334043/295147905179352825856),(44507788207/442721857769029238784),(-5/9223372036854775808),(-1/27670116110564327424)]
  c := (1483598662383/147573952589676412928)
  R := (-460384232913927/50000000000000)
  total := (-22029727/50000000000000)
  k := 27
  n := 32
  sFloor := (2199023216479/4398046511104)
  nFloor := (554347939059/37778931862957161709568)
  eFloor := (1619414982069/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell051
