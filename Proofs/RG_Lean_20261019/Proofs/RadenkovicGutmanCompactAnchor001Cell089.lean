/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell089
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (618221/34359738368)
  b := (680043/34359738368)
  s := [(4398028523167/4398046511104),(-1798779/2199023255552),(-5621/137438953472)]
  L := [(308531869123/144115188075855872),(2961887846347/6917529027641081856),(74045745841/3458764513820540928),(-16645/432345564227567616),(-205/216172782113783808)]
  c := (308531869123/144115188075855872)
  R := (-326357457837059/50000000000000)
  total := (-2914231031/250000000000000)
  k := 19
  n := 32
  sFloor := (549753093217/1099511627776)
  nFloor := (573807190599/36893488147419103232)
  eFloor := (274055251301/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell089
