/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (679931/70368744177664)
  b := (186981/17592186044416)
  s := [(2199023255549/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(210094143769764760706692191/340282366920938463463374607431768211456),(55980243049/453347182355485940514816),(22392064255/3626777458843887524118528),(5/453347182355485940514816),(-1/226673591177742970257408)]
  c := (1492808676813/2417851639229258349412352)
  R := (-1405662057294563/100000000000000)
  total := (-13535279/1000000000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (694077795615/154742504910672534362390528)
  eFloor := (662995055985/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell010
