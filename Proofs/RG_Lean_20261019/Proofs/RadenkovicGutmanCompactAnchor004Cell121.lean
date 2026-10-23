/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (815799/2147483648)
  b := (448689/1073741824)
  s := [(2180736664625/2199023255552),(-7223059659/4398046511104),(-170078469/2199023255552)]
  L := [(112690484832229388720237/19342813113834066795298816),(1951059292321/1688849860263936),(47118227119/844424930131968),(-5073205/26388279066624),(-222949/52776558133248)]
  c := (819931191161/140737488355328)
  R := (-257271561292597/100000000000000)
  total := (-11988828619/125000000000000)
  k := 8
  n := 32
  sFloor := (1088477528163/2199023255552)
  nFloor := (1456641283053/144115188075855872)
  eFloor := (1043920551213/144115188075855872)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell121
