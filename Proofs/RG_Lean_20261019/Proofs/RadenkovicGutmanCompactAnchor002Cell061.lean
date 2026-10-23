/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell061
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (21435/17179869184)
  b := (47157/34359738368)
  s := [(4398046076631/4398046511104),(-86893/4398046511104),(-2173/2199023255552)]
  L := [(4990411247809/73786976294838206464),(2994246446513/221360928884514619392),(24952043653/36893488147419103232),(-383/13835058055282163712),(-1/2305843009213693952)]
  c := (77975175747/1152921504606846976)
  R := (-103182340501687/12500000000000)
  total := (-204773957/200000000000000)
  k := 24
  n := 32
  sFloor := (274877874087/549755813888)
  nFloor := (466167923039/4722366482869645213696)
  eFloor := (1361814964129/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell061
