/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (748047/34359738368)
  b := (1645703/68719476736)
  s := [(4398020175075/4398046511104),(-5267141/4398046511104),(-131673/2199023255552)]
  L := [(127147896915747485206566369/40564819207303340847894502572032),(4336472580043/6917529027641081856),(108408672271/3458764513820540928),(-35629/432345564227567616),(-451/216172782113783808)]
  c := (1806880290413/576460752303423488)
  R := (-3960331492309/625000000000)
  total := (-6844930131/500000000000000)
  k := 19
  n := 32
  sFloor := (1099503661147/2199023255552)
  nFloor := (13126721857/576460752303423488)
  eFloor := (200621929405/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell091
