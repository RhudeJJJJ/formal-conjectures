/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1383919/8589934592)
  b := (761155/4294967296)
  s := [(4390820312023/4398046511104),(-360414233/1099511627776),(-17812487/1099511627776)]
  L := [(22298761265849218017822903/19807040628566084398385987584),(1012321601989/4503599627370496),(75414073247/6755399441055744),(-2114447/281474976710656),(-77387/422212465065984)]
  c := (1267537826711/1125899906842624)
  R := (-339463080623593/100000000000000)
  total := (-53911865327/1000000000000000)
  k := 10
  n := 32
  sFloor := (2194653702571/4398046511104)
  nFloor := (474414262437/288230376151711744)
  eFloor := (1385905508961/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell112
