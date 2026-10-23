/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell247
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (511093/8192)
  b := (281101/4096)
  s := [(4742583636991/2305843009213693952),(-175335078887/288230376151711744),(55980819837/576460752303423488)]
  L := [(151192678699699565020599/151115727451828646838272),(-1337013929/13194139533312),(33208947/2199023255552),(-1610779/824633720832),(25693/137438953472)]
  c := (549987383139/549755813888)
  R := (21056666233/100000000000000)
  total := (1444394165331/1000000000000000)
  k := 0
  n := 32
  sFloor := (1781913142621/2305843009213693952)
  nFloor := 4493083189861353561933093789729850791835594743977221155860863203811668277853431072946235899904
  eFloor := 4490777910251648876319665457849057425029501855431545769908177943161010909243706441987577085952
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell247
