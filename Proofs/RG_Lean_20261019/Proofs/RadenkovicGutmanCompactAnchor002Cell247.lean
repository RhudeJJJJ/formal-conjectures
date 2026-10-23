/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell247
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (511093/8192)
  b := (281101/4096)
  s := [(4742583636991/2305843009213693952),(-175335078887/288230376151711744),(55980819837/576460752303423488)]
  L := [(302385357399255310197199/302231454903657293676544),(-1337013929/13194139533312),(33208947/2199023255552),(-1610779/824633720832),(25693/137438953472)]
  c := (549987383139/549755813888)
  R := (21056666233/100000000000000)
  total := (1444394163847/1000000000000000)
  k := 0
  n := 32
  sFloor := (1781913142621/2305843009213693952)
  nFloor := 296249787685541768560497107205885831060822828056062949907774190874083842633623798808576
  eFloor := 296097789922371661046517739793493974220578309965114745669439723642490836208788730544128
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell247
