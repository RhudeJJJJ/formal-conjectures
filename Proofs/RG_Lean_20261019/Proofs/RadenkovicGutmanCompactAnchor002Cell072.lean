/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (244625/68719476736)
  b := (538175/137438953472)
  s := [(2199021487209/2199023255552),(-353667/2199023255552),(-4421/549755813888)]
  L := [(317366273675/576460752303423488),(507785620735/4611686018427387904),(4760474551/864691128455135232),(-521/288230376151711744),(-5/108086391056891904)]
  c := (317366273675/576460752303423488)
  R := (-90077257948479/12500000000000)
  total := (-254799753/100000000000000)
  k := 21
  n := 32
  sFloor := (1099510557929/2199023255552)
  nFloor := (474337127063/590295810358705651712)
  eFloor := (692839817863/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell072
