/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell032
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1383695/17592186044416)
  b := (95129/1099511627776)
  s := [(4398046509377/4398046511104),(-345/4398046511104),(-9/2199023255552)]
  L := [(5077035492563/18889465931478580854784),(253850857231/4722366482869645213696),(38077490911/14167099448608935641088),(1/590295810358705651712),(-1/885443715538058477568)]
  c := (317314718285/1180591620717411303424)
  R := (-550928567967843/50000000000000)
  total := (-86284377/1000000000000000)
  k := 32
  n := 32
  sFloor := (2199023254507/4398046511104)
  nFloor := (948519364451/2417851639229258349412352)
  eFloor := (692726698045/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell032
