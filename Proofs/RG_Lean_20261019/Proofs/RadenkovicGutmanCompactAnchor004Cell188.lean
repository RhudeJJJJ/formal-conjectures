/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell188
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1890779/8388608)
  b := (129991/524288)
  s := [(2325404370715/8796093022208),(-3821940505/4398046511104),(-4410077545/4398046511104)]
  L := [(3410694581396757107989/4722366482869645213696),(61224431075/8796093022208),(31393321793/13194139533312),(-147195489/549755813888),(14040667/824633720832)]
  c := (794114214693/1099511627776)
  R := (-3253940873289/20000000000000)
  total := (-3601723546621/1000000000000000)
  k := 1
  n := 32
  sFloor := (1154470167307/8796093022208)
  nFloor := (1625032757257/17179869184)
  eFloor := (1309080077317/17179869184)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell188
