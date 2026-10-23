/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (815799/2147483648)
  b := (448689/1073741824)
  s := [(1097512783339/1099511627776),(-99653731/274877906944),(-19662895/1099511627776)]
  L := [(18865230010025607520952445/19807040628566084398385987584),(642126509807/3377699720527872),(10616538205/1125899906842624),(-3189259/422212465065984),(-12919/70368744177664)]
  c := (1072364171365/1125899906842624)
  R := (-347823609750749/100000000000000)
  total := (-26059387391/200000000000000)
  k := 11
  n := 32
  sFloor := (68568406595/137438953472)
  nFloor := (999196185353/144115188075855872)
  eFloor := (477224105833/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell121
