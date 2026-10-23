/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell180
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (882065/8388608)
  b := (1940543/16777216)
  s := [(6742878722129/35184372088832),(355170234721/35184372088832),(-6860142911/17592186044416)]
  L := [(7999024139815654225913/9444732965739290427392),(-153840477451/6597069766656),(1517206301/1099511627776),(4199065/103079215104),(-583087/68719476736)]
  c := (1814243113797/2199023255552)
  R := (-4808623087/50000000000)
  total := (-943558042791/1000000000000000)
  k := 1
  n := 32
  sFloor := (421429920133/4398046511104)
  nFloor := (701640529229/549755813888)
  eFloor := (1123966448425/1099511627776)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell180
