/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell195
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (460573/1048576)
  b := (253315/524288)
  s := [(7405121186545/35184372088832),(-426360027035/35184372088832),(1923195311/17592186044416)]
  L := [(2065823538584385861719/2361183241434822606848),(144402209387/4398046511104),(-979155701/2199023255552),(-5145781/34359738368),(2364375/137438953472)]
  c := (1923948096655/2199023255552)
  R := (-3340847798503/50000000000000)
  total := (-2532255648837/1000000000000000)
  k := 1
  n := 32
  sFloor := (1745651887533/17592186044416)
  nFloor := (553587892985/67108864)
  eFloor := (825412618463/134217728)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell195
