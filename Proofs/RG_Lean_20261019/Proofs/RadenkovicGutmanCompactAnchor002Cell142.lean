/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell142
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (754633/268435456)
  b := (51881/16777216)
  s := [(3115823285513/4398046511104),(-307229679039/8796093022208),(4228821033/4398046511104)]
  L := [(1103297458280982687187/4722366482869645213696),(288033758427/8796093022208),(-203612449/1099511627776),(-33339487/549755813888),(18527/4294967296)]
  c := (2055051658825/8796093022208)
  R := (-36350166560063/50000000000000)
  total := (-194997943933/1000000000000000)
  k := 3
  n := 32
  sFloor := (1483218633513/4398046511104)
  nFloor := (564612255019/1125899906842624)
  eFloor := (206199376451/562949953421312)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell142
