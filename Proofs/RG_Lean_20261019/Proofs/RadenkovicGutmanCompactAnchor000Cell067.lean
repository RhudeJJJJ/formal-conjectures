/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (607573/274877906944)
  b := (334165/137438953472)
  s := [(2199022482149/2199023255552),(-309361/4398046511104),(-7733/2199023255552)]
  L := [(4338043037137/18446744073709551616),(1301406018845/27670116110564327424),(32534943193/13835058055282163712),(-73/216172782113783808),(-7/864691128455135232)]
  c := (271127689821/1152921504606846976)
  R := (-190787188832373/25000000000000)
  total := (-1676108827/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022319735/4398046511104)
  nFloor := (1309271427797/4722366482869645213696)
  eFloor := (979042365335/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell067
