/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1183985/274877906944)
  b := (1302383/274877906944)
  s := [(4398045459329/4398046511104),(-210353/4398046511104),(-5259/2199023255552)]
  L := [(1152924159315/9223372036854775808),(691751393057/27670116110564327424),(34587387319/27670116110564327424),(-7/54043195528445952),(-7/1729382256910270464)]
  c := (1152924159315/9223372036854775808)
  R := (-31789899594109/4000000000000)
  total := (-850590327/250000000000000)
  k := 23
  n := 32
  sFloor := (2199022619229/4398046511104)
  nFloor := (142713484205/147573952589676412928)
  eFloor := (546068061249/590295810358705651712)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell074
