/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell041
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (203917/1099511627776)
  b := (448617/2199023255552)
  s := [(34359738293/34359738368),(-15/34359738368),(-3/137438953472)]
  L := [(496587857959929338172834277/332306998946228968225951765070086144),(2117060601985/7083549724304467820544),(17641998477/1180591620717411303424),(5/442721857769029238784),(-1/73786976294838206464)]
  c := (441058618925/295147905179352825856)
  R := (-1016078232589203/100000000000000)
  total := (-187543743/1000000000000000)
  k := 30
  n := 32
  sFloor := (137438953109/274877906944)
  nFloor := (329603873983/151115727451828646838272)
  eFloor := (481435407319/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell041
