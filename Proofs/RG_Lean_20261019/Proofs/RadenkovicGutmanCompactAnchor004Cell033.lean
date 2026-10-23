/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell033
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (95129/1099511627776)
  b := (837135/8796093022208)
  s := [(2199023254591/2199023255552),(-385/4398046511104),(-9/2199023255552)]
  L := [(1439354762061/4722366482869645213696),(575740391507/9444732965739290427392),(43180415837/14167099448608935641088),(-1/295147905179352825856),(1/885443715538058477568)]
  c := (1439354762061/4722366482869645213696)
  R := (-54778452382801/5000000000000)
  total := (-94368837/1000000000000000)
  k := 32
  n := 32
  sFloor := (2199023254389/4398046511104)
  nFloor := (633805696091/1208925819614629174706176)
  eFloor := (454223690331/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell033
