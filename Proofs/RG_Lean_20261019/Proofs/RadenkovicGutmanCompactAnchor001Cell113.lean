/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (761155/4294967296)
  b := (1674541/8589934592)
  s := [(2198151253705/2199023255552),(-348581883/4398046511104),(-8688983/2199023255552)]
  L := [(467489068661/2251799813685248),(2242970134237/54043195528445952),(55976565239/27021597764222976),(-1219843/3377699720527872),(-15155/1688849860263936)]
  c := (467489068661/2251799813685248)
  R := (-211996610142469/50000000000000)
  total := (-37141354463/500000000000000)
  k := 13
  n := 32
  sFloor := (549492068445/1099511627776)
  nFloor := (434906579279/288230376151711744)
  eFloor := (830860275369/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell113
