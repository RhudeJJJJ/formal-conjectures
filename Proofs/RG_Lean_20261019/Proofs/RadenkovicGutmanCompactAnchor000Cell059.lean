/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1133753/1099511627776)
  b := (155891/137438953472)
  s := [(4398046174471/4398046511104),(-263/17179869184),(-841/1099511627776)]
  L := [(8503617796057244970260220107/166153499473114484112975882535043072),(70806649141/6917529027641081856),(28322575885/55340232221128654848),(-7/432345564227567616),(-1/3458764513820540928)]
  c := (944091226979/18446744073709551616)
  R := (-209849136483311/25000000000000)
  total := (-860543687/1000000000000000)
  k := 25
  n := 32
  sFloor := (2199023051889/4398046511104)
  nFloor := (1139750169621/18889465931478580854784)
  eFloor := (852278357427/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell059
