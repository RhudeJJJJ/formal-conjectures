/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell165
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (211161/8388608)
  b := (232277/8388608)
  s := [(5752444524515/17592186044416),(-58911425805/4398046511104),(3718062189/2199023255552)]
  L := [(5041265926189659463007/9444732965739290427392),(54943352273/3298534883328),(-13933718923/6597069766656),(8709157/51539607552),(-4013021/412316860416)]
  c := (1173761190425/2199023255552)
  R := (-1961875005081/6250000000000)
  total := (-386125152859/500000000000000)
  k := 1
  n := 32
  sFloor := (1386635829701/8796093022208)
  nFloor := (1136831223065/35184372088832)
  eFloor := (540096406419/17592186044416)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell165
