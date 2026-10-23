/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (656819/2199023255552)
  b := (1445001/4398046511104)
  s := [(1099511621551/1099511627776),(-4979/4398046511104),(-125/2199023255552)]
  L := [(1143986418317/295147905179352825856),(457591777945/590295810358705651712),(11439724531/295147905179352825856),(-7/36893488147419103232),(1/18446744073709551616)]
  c := (1143986418317/295147905179352825856)
  R := (-968423407068057/100000000000000)
  total := (-143903809/500000000000000)
  k := 28
  n := 32
  sFloor := (2199023240487/4398046511104)
  nFloor := (1709806091181/302231454903657293676544)
  eFloor := (624356429733/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell046
