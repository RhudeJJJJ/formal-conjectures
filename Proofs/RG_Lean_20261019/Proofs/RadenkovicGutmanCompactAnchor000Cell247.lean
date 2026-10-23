/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell247
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (511093/8192)
  b := (281101/4096)
  s := [(4742583636991/2305843009213693952),(-175335078887/288230376151711744),(55980819837/576460752303423488)]
  L := [(75596339349775979488661/75557863725914323419136),(-1337013929/13194139533312),(33208947/2199023255552),(-1610779/824633720832),(25693/137438953472)]
  c := (1099974766277/1099511627776)
  R := (21056666187/100000000000000)
  total := (1444394162251/1000000000000000)
  k := 0
  n := 32
  sFloor := (1781913142621/2305843009213693952)
  nFloor := 19533120798158526463476419889154912857937233899718928683956620510978272986660864
  eFloor := 19523098881543535754428653648055379029424782949294967837985538989225274563887104
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell247
