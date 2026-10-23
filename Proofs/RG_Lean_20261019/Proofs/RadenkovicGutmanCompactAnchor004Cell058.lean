/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1030685/1099511627776)
  b := (1133753/1099511627776)
  s := [(1099511571389/1099511627776),(-11277/1099511627776),(-141/274877906944)]
  L := [(92888875545572341820781767/2596148429267413814265248164610048),(1584028610503/221360928884514619392),(19800257399/55340232221128654848),(-47/6917529027641081856),(-1/1729382256910270464)]
  c := (330007578759/9223372036854775808)
  R := (-857294545909849/100000000000000)
  total := (-399544311/500000000000000)
  k := 25
  n := 32
  sFloor := (274877889887/549755813888)
  nFloor := (1162524762283/18889465931478580854784)
  eFloor := (1666271827125/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell058
