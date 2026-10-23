/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell027
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (859167/17592186044416)
  b := (945083/17592186044416)
  s := [(4398046510491/4398046511104),(-15/549755813888),(-1/549755813888)]
  L := [(7337991072055/75557863725914323419136),(1467586257037/75557863725914323419136),(110068072543/113336795588871485128704),(-7/4722366482869645213696),(5/7083549724304467820544)]
  c := (1834497768013/18889465931478580854784)
  R := (-144094371858551/12500000000000)
  total := (-448491/8000000000000)
  k := 34
  n := 32
  sFloor := (2199023255181/4398046511104)
  nFloor := (1615606055055/9671406556917033397649408)
  eFloor := (1157841510377/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell027
