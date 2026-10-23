/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell137
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (937137/536870912)
  b := (515425/268435456)
  s := [(934233365773/1099511627776),(-103583466411/4398046511104),(-229237943/2199023255552)]
  L := [(33629730383325103044573/302231454903657293676544),(1987566963143/105553116266496),(6741351161/17592186044416),(-235633241/6597069766656),(957451/1099511627776)]
  c := (1957507942763/17592186044416)
  R := (-54894565555721/50000000000000)
  total := (-184558685261/1000000000000000)
  k := 4
  n := 32
  sFloor := (1816445760397/4398046511104)
  nFloor := (1740767762151/9007199254740992)
  eFloor := (1271382858695/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell137
