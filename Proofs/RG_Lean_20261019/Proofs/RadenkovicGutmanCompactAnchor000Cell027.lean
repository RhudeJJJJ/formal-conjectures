/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell027
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (859167/17592186044416)
  b := (945083/17592186044416)
  s := [(1099511627587/1099511627776),(-75/2199023255552),(-1/549755813888)]
  L := [(4337327938379/37778931862957161709568),(2602375559729/113336795588871485128704),(21686286307/18889465931478580854784),(-11/7083549724304467820544),(1/1180591620717411303424)]
  c := (2168663969189/18889465931478580854784)
  R := (-1144387947498333/100000000000000)
  total := (-55652749/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255095/4398046511104)
  nFloor := (5113496615/37778931862957161709568)
  eFloor := (978880625451/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell027
