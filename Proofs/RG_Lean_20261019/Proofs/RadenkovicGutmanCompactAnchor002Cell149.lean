/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell149
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1470563/268435456)
  b := (1617619/268435456)
  s := [(4075228945251/8796093022208),(-306723165145/8796093022208),(10054818857/4398046511104)]
  L := [(4741084718984785657763/9444732965739290427392),(1177344385589/26388279066624),(-27949963285/13194139533312),(85921027/1649267441664),(1599469/824633720832)]
  c := (551934903369/1099511627776)
  R := (-3445956374039/10000000000000)
  total := (-44326547171/250000000000000)
  k := 1
  n := 32
  sFloor := (947153854455/4398046511104)
  nFloor := (537004767467/281474976710656)
  eFloor := (1569453457139/1125899906842624)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell149
