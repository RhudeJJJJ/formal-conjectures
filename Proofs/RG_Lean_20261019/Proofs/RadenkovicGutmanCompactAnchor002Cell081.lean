/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell081
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1153623/137438953472)
  b := (1268985/137438953472)
  s := [(1099506711909/1099511627776),(-3932657/4398046511104),(-98313/2199023255552)]
  L := [(124166685960114079022968517/40564819207303340847894502572032),(2117402504171/3458764513820540928),(52933957729/1729382256910270464),(-12065/216172782113783808),(-157/108086391056891904)]
  c := (1764514734647/576460752303423488)
  R := (-634839341120119/100000000000000)
  total := (-1057602873/200000000000000)
  k := 19
  n := 32
  sFloor := (274876419897/549755813888)
  nFloor := (659315480697/147573952589676412928)
  eFloor := (481514087653/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell081
