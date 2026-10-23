/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (815799/2147483648)
  b := (448689/1073741824)
  s := [(1089580434871/1099511627776),(-1959272493/1099511627776),(-91790653/1099511627776)]
  L := [(961236718971700256555639/154742504910672534362390528),(43308125951/35184372088832),(4171259605/70368744177664),(-3898155/17592186044416),(-10583/2199023255552)]
  c := (437119851527/70368744177664)
  R := (-63516213144133/25000000000000)
  total := (-94693856987/1000000000000000)
  k := 8
  n := 32
  sFloor := (1087529371725/2199023255552)
  nFloor := (329713681505/36028797018963968)
  eFloor := (240798418623/36028797018963968)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell121
