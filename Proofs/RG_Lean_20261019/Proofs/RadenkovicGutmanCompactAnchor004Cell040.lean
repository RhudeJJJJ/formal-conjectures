/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell040
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1483033/8796093022208)
  b := (203917/1099511627776)
  s := [(4398046503807/4398046511104),(-365/1099511627776),(-9/549755813888)]
  L := [(5465924661821/4722366482869645213696),(1639774078655/7083549724304467820544),(13664756279/1180591620717411303424),(-17/442721857769029238784),(1/73786976294838206464)]
  c := (1366481165455/1180591620717411303424)
  R := (-514426064500797/50000000000000)
  total := (-43162339/250000000000000)
  k := 30
  n := 32
  sFloor := (2199023251137/4398046511104)
  nFloor := (601716526169/302231454903657293676544)
  eFloor := (862453280983/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell040
