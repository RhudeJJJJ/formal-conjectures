/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell045
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1194217/4398046511104)
  b := (656819/2199023255552)
  s := [(4398046507007/4398046511104),(-819/4398046511104),(-21/2199023255552)]
  L := [(324056520459919007963560951/664613997892457936451903530140172288),(921018626751/9444732965739290427392),(69075991891/14167099448608935641088),(-7/590295810358705651712),(5/885443715538058477568)]
  c := (575640016471/1180591620717411303424)
  R := (-1072077715416721/100000000000000)
  total := (-289788941/1000000000000000)
  k := 31
  n := 32
  sFloor := (2199023253073/4398046511104)
  nFloor := (535284876511/151115727451828646838272)
  eFloor := (127828331677/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell045
