/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (829963/549755813888)
  b := (912959/549755813888)
  s := [(4398045874993/4398046511104),(-127221/4398046511104),(-3181/2199023255552)]
  L := [(456653577773/4611686018427387904),(1095964463203/55340232221128654848),(13699498183/13835058055282163712),(-205/3458764513820540928),(-1/864691128455135232)]
  c := (456653577773/4611686018427387904)
  R := (-806396714491893/100000000000000)
  total := (-605049997/500000000000000)
  k := 24
  n := 32
  sFloor := (2199022870705/4398046511104)
  nFloor := (85314515903/590295810358705651712)
  eFloor := (498458082049/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell063
