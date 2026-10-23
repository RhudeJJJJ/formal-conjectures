/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1535471/137438953472)
  b := (844509/68719476736)
  s := [(4398011676309/4398046511104),(-870859/549755813888),(-87081/1099511627776)]
  L := [(3125929533083/576460752303423488),(937770661247/864691128455135232),(23443492483/432345564227567616),(-18973/108086391056891904),(-59/13510798882111488)]
  c := (1562964766541/288230376151711744)
  R := (-151561635594541/25000000000000)
  total := (-3359458107/500000000000000)
  k := 18
  n := 32
  sFloor := (549750545139/1099511627776)
  nFloor := (292003938027/36893488147419103232)
  eFloor := (1706060470787/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell084
