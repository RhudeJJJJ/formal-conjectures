/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell181
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1940543/16777216)
  b := (533649/4194304)
  s := [(1771082167757/8796093022208),(90096869503/8796093022208),(-4771733375/8796093022208)]
  L := [(3896057419276098889191/4722366482869645213696),(-148555887593/6597069766656),(2898198277/1649267441664),(7607437/824633720832),(-1578539/206158430208)]
  c := (1768592197205/2199023255552)
  R := (-1089147128639/10000000000000)
  total := (-1187833061421/1000000000000000)
  k := 1
  n := 32
  sFloor := (1771082167757/17592186044416)
  nFloor := (970822193687/549755813888)
  eFloor := (1564559634265/1099511627776)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell181
