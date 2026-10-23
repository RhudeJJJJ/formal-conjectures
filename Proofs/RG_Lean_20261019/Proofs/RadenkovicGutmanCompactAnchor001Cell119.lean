/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1348429/4294967296)
  b := (1483271/4294967296)
  s := [(4392580518771/4398046511104),(-1091041791/4398046511104),(-27025319/2199023255552)]
  L := [(25786772005913331764904047/39614081257132168796771975168),(3513113731559/27021597764222976),(29115928437/4503599627370496),(-5973977/1688849860263936),(-24417/281474976710656)]
  c := (183226035275/281474976710656)
  R := (-366853913692083/100000000000000)
  total := (-56828780191/500000000000000)
  k := 11
  n := 32
  sFloor := (2195717713171/4398046511104)
  nFloor := (85307797539/18014398509481984)
  eFloor := (651899260189/144115188075855872)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell119
