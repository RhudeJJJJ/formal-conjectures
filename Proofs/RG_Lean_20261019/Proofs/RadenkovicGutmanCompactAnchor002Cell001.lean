/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1153433/281474976710656)
  b := (158597/35184372088832)
  s := [(4398046511099/4398046511104),(-3/4398046511104),(1/2199023255552)]
  L := [(3527883226481/4835703278458516698824704),(132295276901/906694364710971881029632),(13229493275/1813388729421943762059264),(7/906694364710971881029632),(-1/226673591177742970257408)]
  c := (220492701655/302231454903657293676544)
  R := (-698658741286513/50000000000000)
  total := (-5706101/1000000000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (329549159091/309485009821345068724781056)
  eFloor := (481355488093/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell001
