/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell225
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (2009161/262144)
  b := (552519/65536)
  s := [(584775224857/562949953421312),(-1326940922367/4503599627370496),(101646377025/2251799813685248)]
  L := [(4863597386840098485685/4722366482869645213696),(-71328327929/13194139533312),(1565596727/2199023255552),(-65399359/824633720832),(901161/137438953472)]
  c := (563576645615/549755813888)
  R := (620728410047/50000000000000)
  total := (2591722893499/250000000000000)
  k := 0
  n := 32
  sFloor := (1777276815269/4503599627370496)
  nFloor := 766366073434515113287228325272393721759924224
  eFloor := 742567738390670739980166357773077327101558784
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell225
