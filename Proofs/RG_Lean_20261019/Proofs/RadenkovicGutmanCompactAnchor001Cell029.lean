/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1039591/17592186044416)
  b := (571775/8796093022208)
  s := [(4398046510909/4398046511104),(-9/1099511627776),(-1/1099511627776)]
  L := [(3489791560795/151115727451828646838272),(2093872922257/453347182355485940514816),(52346772661/226673591177742970257408),(5/28334198897217871282176),(-1/14167099448608935641088)]
  c := (1744895780397/75557863725914323419136)
  R := (-306143372218217/25000000000000)
  total := (-72078711/1000000000000000)
  k := 36
  n := 32
  sFloor := (1099511627717/2199023255552)
  nFloor := (405642543383/2417851639229258349412352)
  eFloor := (96869184715/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell029
