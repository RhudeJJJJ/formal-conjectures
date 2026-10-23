/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell102
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1067127/17179869184)
  b := (1173839/17179869184)
  s := [(4396825476415/4398046511104),(-244103447/4398046511104),(-6090641/2199023255552)]
  L := [(235356519242428721003551251/1267650600228229401496703205376),(1003094785543/27021597764222976),(12524416481/6755399441055744),(-354397/1688849860263936),(-2207/422212465065984)]
  c := (836154325307/4503599627370496)
  R := (-13424334931989/3125000000000)
  total := (-3297814001/125000000000000)
  k := 13
  n := 32
  sFloor := (2198284595843/4398046511104)
  nFloor := (504864816865/2305843009213693952)
  eFloor := (1510104185851/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell102
