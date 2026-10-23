/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell027
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (859167/17592186044416)
  b := (945083/17592186044416)
  s := [(2199023255219/2199023255552),(-33/1099511627776),(-1/549755813888)]
  L := [(1957422751159/18889465931478580854784),(1174444081735/56668397794435742564352),(305842321/295147905179352825856),(-1/3541774862152233910272)]
  c := (1957422751159/18889465931478580854784)
  R := (-287378019505159/25000000000000)
  total := (-55902999/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255149/4398046511104)
  nFloor := (1462785427561/9671406556917033397649408)
  eFloor := (16692307459/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell027
