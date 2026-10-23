/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (337053/2199023255552)
  b := (1483033/8796093022208)
  s := [(4398046505073/4398046511104),(-603/2199023255552),(-15/1099511627776)]
  L := [(1129323582167/1180591620717411303424),(903457524231/4722366482869645213696),(67759213439/7083549724304467820544),(-3/295147905179352825856),(1/442721857769029238784)]
  c := (1129323582167/1180591620717411303424)
  R := (-1038383133481401/100000000000000)
  total := (-158414919/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023251903/4398046511104)
  nFloor := (994573038781/604462909807314587353088)
  eFloor := (178192874711/151115727451828646838272)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell039
