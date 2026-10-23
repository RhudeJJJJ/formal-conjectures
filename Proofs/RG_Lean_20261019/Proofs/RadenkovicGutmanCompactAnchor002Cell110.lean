/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (142967/1073741824)
  b := (1258109/8589934592)
  s := [(4393106996749/4398046511104),(-986227747/4398046511104),(-24460829/2199023255552)]
  L := [(60953989033399460715651587/79228162514264337593543950336),(1038251868637/6755399441055744),(12918534569/1688849860263936),(-2968937/844424930131968),(-18253/211106232532992)]
  c := (1732416564931/2251799813685248)
  R := (-17924919501191/5000000000000)
  total := (-23544754293/500000000000000)
  k := 11
  n := 32
  sFloor := (274504490459/549755813888)
  nFloor := (648063670265/576460752303423488)
  eFloor := (118324185651/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell110
