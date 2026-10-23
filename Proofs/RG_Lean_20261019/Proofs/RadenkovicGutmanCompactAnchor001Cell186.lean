/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell186
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (390657/2097152)
  b := (859445/4194304)
  s := [(5389979637853/17592186044416),(-103861960127/17592186044416),(-3227504567/8796093022208)]
  L := [(5987166306095954864895/9444732965739290427392),(18382888459/1099511627776),(485185121/824633720832),(-12666057/137438953472),(685223/103079215104)]
  c := (1393995784711/2199023255552)
  R := (-22791949928783/100000000000000)
  total := (-2060692941951/500000000000000)
  k := 1
  n := 32
  sFloor := (329978916787/2199023255552)
  nFloor := (1079490643865/68719476736)
  eFloor := (904137867751/68719476736)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell186
