/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (761155/4294967296)
  b := (1674541/8589934592)
  s := [(68564638921/68719476736),(-987608247/2199023255552),(-24300117/1099511627776)]
  L := [(14937378727927158843563699/9903520314283042199192993792),(1016570873081/3377699720527872),(25181024783/1688849860263936),(-5798569/422212465065984),(-4381/13194139533312)]
  c := (424545837857/281474976710656)
  R := (-162419471229791/50000000000000)
  total := (-28356134401/500000000000000)
  k := 10
  n := 32
  sFloor := (2193032236991/4398046511104)
  nFloor := (513712271737/288230376151711744)
  eFloor := (1536568336967/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell113
