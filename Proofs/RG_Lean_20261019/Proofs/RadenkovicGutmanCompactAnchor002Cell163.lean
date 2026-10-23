/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell163
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1396107/67108864)
  b := (1535717/67108864)
  s := [(6046042824537/35184372088832),(-159680151145/17592186044416),(9685521881/8796093022208)]
  L := [(567637764901028194811/590295810358705651712),(27906141559/1649267441664),(-8050655231/3298534883328),(84435509/412316860416),(-2902435/206158430208)]
  c := (1057307729313/1099511627776)
  R := (-978507682851/50000000000000)
  total := (-32432208801/1000000000000000)
  k := 1
  n := 32
  sFloor := (720678076221/8796093022208)
  nFloor := (62534767771/2199023255552)
  eFloor := (735337785707/35184372088832)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell163
