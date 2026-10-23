/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1030685/1099511627776)
  b := (1133753/1099511627776)
  s := [(2199023231139/2199023255552),(-4883/2199023255552),(-61/549755813888)]
  L := [(107195460333/18446744073709551616),(343023804813/295147905179352825856),(6431664835/110680464442257309696),(-1/2305843009213693952),(1/13835058055282163712)]
  c := (107195460333/18446744073709551616)
  R := (-1896349981879/200000000000)
  total := (-884279769/1000000000000000)
  k := 28
  n := 32
  sFloor := (549755806503/1099511627776)
  nFloor := (199361085923/4722366482869645213696)
  eFloor := (761732561721/18889465931478580854784)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell058
