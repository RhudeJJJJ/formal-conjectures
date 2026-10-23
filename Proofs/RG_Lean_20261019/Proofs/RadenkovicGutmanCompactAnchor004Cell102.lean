/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1067127/17179869184)
  b := (1173839/17179869184)
  s := [(4397056525281/4398046511104),(-197928681/4398046511104),(-4940333/2199023255552)]
  L := [(2829398598919/18014398509481984),(1697236825609/54043195528445952),(42391533917/27021597764222976),(-488569/3377699720527872),(-6089/1688849860263936)]
  c := (1414699299459/9007199254740992)
  R := (-87588624544529/20000000000000)
  total := (-6725511629/250000000000000)
  k := 13
  n := 32
  sFloor := (2198424357967/4398046511104)
  nFloor := (1246185454045/4611686018427387904)
  eFloor := (1786184632679/9223372036854775808)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell102
