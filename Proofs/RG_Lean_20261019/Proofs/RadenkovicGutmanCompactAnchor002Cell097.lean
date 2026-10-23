/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell097
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1325207/34359738368)
  b := (1457727/34359738368)
  s := [(4397631403857/4398046511104),(-83009217/4398046511104),(-2073839/2199023255552)]
  L := [(582056353115/9007199254740992),(698396587807/54043195528445952),(34906177327/54043195528445952),(-168305/6755399441055744),(-2101/3377699720527872)]
  c := (582056353115/9007199254740992)
  R := (-482348373151429/100000000000000)
  total := (-18416728141/1000000000000000)
  k := 14
  n := 32
  sFloor := (2198772123481/4398046511104)
  nFloor := (435013724071/4611686018427387904)
  eFloor := (79425270237/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell097
