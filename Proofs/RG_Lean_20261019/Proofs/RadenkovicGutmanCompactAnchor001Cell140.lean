/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell140
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (38979/16777216)
  b := (343015/134217728)
  s := [(4127347332421/4398046511104),(-97897940261/8796093022208),(-1399686279/4398046511104)]
  L := [(10046854527876591445627/302231454903657293676544),(2616667174651/422212465065984),(47915571839/211106232532992),(-184120153/26388279066624),(-239339/13194139533312)]
  c := (1169607803211/35184372088832)
  R := (-42549169094823/25000000000000)
  total := (-384982611791/1000000000000000)
  k := 5
  n := 32
  sFloor := (2038499338005/4398046511104)
  nFloor := (584255572365/2251799813685248)
  eFloor := (558065143843/2251799813685248)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell140
