/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (64985/536870912)
  b := (142967/1073741824)
  s := [(274827040151/274877906944),(-162726073/4398046511104),(-4062581/2199023255552)]
  L := [(245602164179938778918737859/2535301200456458802993406410752),(4187408685743/216172782113783808),(104600105783/108086391056891904),(-1063361/13510798882111488),(-13259/6755399441055744)]
  c := (872554168225/9007199254740992)
  R := (-462105499832787/100000000000000)
  total := (-55349294279/1000000000000000)
  k := 14
  n := 32
  sFloor := (1099265447795/2199023255552)
  nFloor := (405775005519/576460752303423488)
  eFloor := (193801610129/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell109
