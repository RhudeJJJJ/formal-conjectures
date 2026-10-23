/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (320039/268435456)
  b := (1408171/1073741824)
  s := [(4048628205185/4398046511104),(-7713661519/549755813888),(-373231247/1099511627776)]
  L := [(17118850017842145451819/302231454903657293676544),(2197181798317/211106232532992),(12475280083/35184372088832),(-176316967/13194139533312),(65569/2199023255552)]
  c := (996448217067/17592186044416)
  R := (-897191541937/625000000000)
  total := (-165870793631/1000000000000000)
  k := 5
  n := 32
  sFloor := (996356497011/2199023255552)
  nFloor := (811974146559/9007199254740992)
  eFloor := (593017022595/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell133
