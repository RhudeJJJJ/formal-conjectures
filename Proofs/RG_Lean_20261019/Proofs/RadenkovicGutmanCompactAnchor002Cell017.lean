/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell017
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1324989/70368744177664)
  b := (1457487/70368744177664)
  s := [(4398046511005/4398046511104),(-23/4398046511104),(1/2199023255552)]
  L := [(4655367839151/302231454903657293676544),(2793201730439/906694364710971881029632),(69829568963/453347182355485940514816),(-5/56668397794435742564352),(1/28334198897217871282176)]
  c := (1163841959787/75557863725914323419136)
  R := (-311205475498937/25000000000000)
  total := (-2334773/100000000000000)
  k := 36
  n := 32
  sFloor := (549755813873/1099511627776)
  nFloor := (13589705021/604462909807314587353088)
  eFloor := (317596518175/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell017
