/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1548741/2199023255552)
  b := (851807/1099511627776)
  s := [(2199023186333/2199023255552),(-27685/4398046511104),(-693/2199023255552)]
  L := [(6360438148665/295147905179352825856),(1272078553779/295147905179352825856),(95405201573/442721857769029238784),(-47/18446744073709551616),(-5/27670116110564327424)]
  c := (795054768583/36893488147419103232)
  R := (-441322247396731/50000000000000)
  total := (-618220493/1000000000000000)
  k := 26
  n := 32
  sFloor := (2199023171797/4398046511104)
  nFloor := (594145830875/18889465931478580854784)
  eFloor := (108479777801/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell055
