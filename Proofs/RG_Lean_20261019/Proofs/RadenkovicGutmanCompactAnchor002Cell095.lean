/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1095213/34359738368)
  b := (602367/17179869184)
  s := [(4397762974051/4398046511104),(-7087719/549755813888),(-22139/34359738368)]
  L := [(6361038563621/144115188075855872),(3816361322411/432345564227567616),(95383637699/216172782113783808),(-314123/27021597764222976),(-3923/13510798882111488)]
  c := (1590259640905/36028797018963968)
  R := (-501408825790051/100000000000000)
  total := (-7914013197/500000000000000)
  k := 15
  n := 32
  sFloor := (2198851719253/4398046511104)
  nFloor := (594241085175/9223372036854775808)
  eFloor := (1735954737291/36893488147419103232)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell095
