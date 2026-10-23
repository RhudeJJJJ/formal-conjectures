/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell106
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (781189/8589934592)
  b := (859307/8589934592)
  s := [(4397587041973/4398046511104),(-45938787/2199023255552),(-1147569/1099511627776)]
  L := [(3940640895425/72057594037927936),(2364085982567/216172782113783808),(19691447105/36028797018963968),(-339011/13510798882111488),(-1409/2251799813685248)]
  c := (61572513991/1125899906842624)
  R := (-122673470269171/25000000000000)
  total := (-44184195771/1000000000000000)
  k := 15
  n := 32
  sFloor := (2198745287061/4398046511104)
  nFloor := (229050400453/576460752303423488)
  eFloor := (437585738249/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell106
