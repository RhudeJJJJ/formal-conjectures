/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1348429/4294967296)
  b := (1483271/4294967296)
  s := [(4392469947119/4398046511104),(-1113072069/4398046511104),(-27566305/2199023255552)]
  L := [(13135618206412503776525223/19807040628566084398385987584),(1789514851127/13510798882111488),(7414841015/1125899906842624),(-3096341/844424930131968),(-6325/70368744177664)]
  c := (1493346895405/2251799813685248)
  R := (-73184652531667/20000000000000)
  total := (-113365418137/1000000000000000)
  k := 11
  n := 32
  sFloor := (548912717805/1099511627776)
  nFloor := (185111568013/36028797018963968)
  eFloor := (354148110403/72057594037927936)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell119
