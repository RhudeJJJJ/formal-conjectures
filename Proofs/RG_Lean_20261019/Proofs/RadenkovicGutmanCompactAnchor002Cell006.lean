/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell006
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (928805/140737488355328)
  b := (2043371/281474976710656)
  s := [(4398046511091/4398046511104),(-1/2199023255552)]
  L := [(321949935152365424844763383/170141183460469231731687303715884105728),(915036750815/2417851639229258349412352),(68627756201/3626777458843887524118528),(7/151115727451828646838272),(-5/226673591177742970257408)]
  c := (142974492313/75557863725914323419136)
  R := (-269932536466939/20000000000000)
  total := (-887523/100000000000000)
  k := 39
  n := 32
  sFloor := (274877906943/549755813888)
  nFloor := (854760694747/309485009821345068724781056)
  eFloor := (1248504934917/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell006
