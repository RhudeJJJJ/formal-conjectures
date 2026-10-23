/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1383919/8589934592)
  b := (761155/4294967296)
  s := [(4396605025415/4398046511104),(-288145747/4398046511104),(-7186129/2199023255552)]
  L := [(6182148286921/36028797018963968),(1235976487773/36028797018963968),(92564154103/54043195528445952),(-555691/2251799813685248),(-20731/3377699720527872)]
  c := (772768535865/4503599627370496)
  R := (-86704079845617/20000000000000)
  total := (-69064186079/1000000000000000)
  k := 13
  n := 32
  sFloor := (2198151253705/4398046511104)
  nFloor := (718854327183/576460752303423488)
  eFloor := (171665468119/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell112
