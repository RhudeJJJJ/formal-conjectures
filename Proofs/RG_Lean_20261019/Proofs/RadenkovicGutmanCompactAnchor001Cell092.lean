/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell092
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1645703/68719476736)
  b := (56571/2147483648)
  s := [(1099503661147/1099511627776),(-6373177/4398046511104),(-159321/2199023255552)]
  L := [(1093160534377/288230376151711744),(2623543677973/3458764513820540928),(21861995289/576460752303423488),(-26095/216172782113783808),(-109/36028797018963968)]
  c := (1093160534377/288230376151711744)
  R := (-624122114156857/100000000000000)
  total := (-3707629667/250000000000000)
  k := 19
  n := 32
  sFloor := (34359437131/68719476736)
  nFloor := (508266428041/18446744073709551616)
  eFloor := (485504837333/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell092
