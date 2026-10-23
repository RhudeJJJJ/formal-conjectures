/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell152
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (978659/134217728)
  b := (269131/33554432)
  s := [(731628680363/1099511627776),(-305229079447/8796093022208),(6280986465/4398046511104)]
  L := [(1987344612816726740071/9444732965739290427392),(2768398177171/105553116266496),(-28037374501/52776558133248),(-244879273/6597069766656),(13361881/3298534883328)]
  c := (115678681341/549755813888)
  R := (-38966446143551/50000000000000)
  total := (-546711159603/1000000000000000)
  k := 3
  n := 32
  sFloor := (43440330753/137438953472)
  nFloor := (722613618405/281474976710656)
  eFloor := (43121185647/17592186044416)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell152
