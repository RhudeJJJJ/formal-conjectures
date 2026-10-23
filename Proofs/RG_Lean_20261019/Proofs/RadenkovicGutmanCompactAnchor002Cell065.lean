/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell065
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (502127/274877906944)
  b := (1104679/549755813888)
  s := [(8589932773/8589934592),(-186263/4398046511104),(-4657/2199023255552)]
  L := [(334292409809/2305843009213693952),(1604596828721/55340232221128654848),(40114726253/27670116110564327424),(-437/3458764513820540928),(-5/1729382256910270464)]
  c := (334292409809/2305843009213693952)
  R := (-787334804438563/100000000000000)
  total := (-1429397889/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022692099/4398046511104)
  nFloor := (249817353541/1180591620717411303424)
  eFloor := (1459581380643/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell065
