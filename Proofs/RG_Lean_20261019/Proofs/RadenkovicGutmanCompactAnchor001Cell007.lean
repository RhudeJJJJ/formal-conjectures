/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (2043371/281474976710656)
  b := (561927/70368744177664)
  s := [(4398046511101/4398046511104),(-3/4398046511104),(1/2199023255552)]
  L := [(6741226530299/19342813113834066795298816),(4044733938725/58028439341502200385896448),(33706099675/9671406556917033397649408),(-11/3626777458843887524118528),(1/604462909807314587353088)]
  c := (842653316287/2417851639229258349412352)
  R := (-717127504123747/50000000000000)
  total := (-5188423/500000000000000)
  k := 42
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (783579256097/309485009821345068724781056)
  eFloor := (374244195713/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell007
