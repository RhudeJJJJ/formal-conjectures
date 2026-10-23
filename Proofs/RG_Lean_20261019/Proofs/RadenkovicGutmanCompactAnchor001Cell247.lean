/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell247
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (511093/8192)
  b := (281101/4096)
  s := [(4742583636991/2305843009213693952),(-175335078887/288230376151711744),(55980819837/576460752303423488)]
  L := [(151192678699607530658067/151115727451828646838272),(-1337013929/13194139533312),(33208947/2199023255552),(-1610779/824633720832),(25693/137438953472)]
  c := (1099974766277/1099511627776)
  R := (21056666187/100000000000000)
  total := (722197081699/500000000000000)
  k := 0
  n := 32
  sFloor := (1781913142621/2305843009213693952)
  nFloor := 76070249699181288033513500335993338458771167095255823677744576513950336081190715392
  eFloor := 76031220109028696966270509767820471633369388808218124414942155212572197992838201344
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell247
