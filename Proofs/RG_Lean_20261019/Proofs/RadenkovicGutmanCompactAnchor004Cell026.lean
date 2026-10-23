/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (781061/17592186044416)
  b := (859167/17592186044416)
  s := [(2199023255299/2199023255552),(-101/4398046511104),(-3/2199023255552)]
  L := [(3032228421653/37778931862957161709568),(1212889815643/75557863725914323419136),(90966619667/113336795588871485128704),(-1/4722366482869645213696),(1/7083549724304467820544)]
  c := (758057105413/9444732965739290427392)
  R := (-1162285981208423/100000000000000)
  total := (-51388399/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255245/4398046511104)
  nFloor := (1335211926563/9671406556917033397649408)
  eFloor := (1913788065957/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell026
