/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (155891/137438953472)
  b := (21435/17179869184)
  s := [(4398046152035/4398046511104),(-17953/1099511627776),(-449/549755813888)]
  L := [(18574248630132141794293433467/332306998946228968225951765070086144),(206214244927/18446744073709551616),(10310642655/18446744073709551616),(-41/2305843009213693952),(-1/1152921504606846976)]
  c := (515538962357/9223372036854775808)
  R := (-834989682802371/100000000000000)
  total := (-941595801/1000000000000000)
  k := 25
  n := 32
  sFloor := (2199023038315/4398046511104)
  nFloor := (1541052782573/18889465931478580854784)
  eFloor := (1125468225125/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell060
