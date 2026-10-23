/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (645611/8589934592)
  b := (177543/2147483648)
  s := [(4396259148553/4398046511104),(-89313409/1099511627776),(-2226457/549755813888)]
  L := [(689078719210207335243032289/2535301200456458802993406410752),(367062289559/6755399441055744),(3053781943/1125899906842624),(-189773/422212465065984),(-393/35184372088832)]
  c := (612024847877/2251799813685248)
  R := (-51315421805103/12500000000000)
  total := (-3811353597/125000000000000)
  k := 12
  n := 32
  sFloor := (1098971020815/2199023255552)
  nFloor := (739170759929/2305843009213693952)
  eFloor := (69091816995/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell104
