/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1483271/4294967296)
  b := (815799/2147483648)
  s := [(2195717713171/2199023255552),(-659535985/2199023255552),(-8152627/549755813888)]
  L := [(15596507027060789706048025/19807040628566084398385987584),(2124226267069/13510798882111488),(52754983993/6755399441055744),(-4365811/844424930131968),(-53317/422212465065984)]
  c := (1773117563409/2251799813685248)
  R := (-178668644002889/50000000000000)
  total := (-121737917491/1000000000000000)
  k := 11
  n := 32
  sFloor := (1097512783339/2199023255552)
  nFloor := (412890052271/72057594037927936)
  eFloor := (394399280589/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell120
