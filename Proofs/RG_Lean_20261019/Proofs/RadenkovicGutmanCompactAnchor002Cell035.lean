/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1841697/17592186044416)
  b := (1012933/8796093022208)
  s := [(4398046508045/4398046511104),(-613/4398046511104),(-15/2199023255552)]
  L := [(4497133932277/9444732965739290427392),(899423367227/9444732965739290427392),(22485498675/4722366482869645213696),(-5/590295810358705651712),(1/295147905179352825856)]
  c := (1124283483069/2361183241434822606848)
  R := (-1073264138750967/100000000000000)
  total := (-27962769/250000000000000)
  k := 31
  n := 32
  sFloor := (2199023253701/4398046511104)
  nFloor := (105022375431/151115727451828646838272)
  eFloor := (613603104627/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell035
