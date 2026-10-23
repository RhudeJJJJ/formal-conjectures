/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell087
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (510927/34359738368)
  b := (1124039/68719476736)
  s := [(34359294979/34359738368),(-2837623/1099511627776),(-35467/274877906944)]
  L := [(91302733177577677858689587/10141204801825835211973625643008),(64873382847/36028797018963968),(202717815/2251799813685248),(-4283/9007199254740992),(-27/2251799813685248)]
  c := (1297489876287/144115188075855872)
  R := (-580896832121859/100000000000000)
  total := (-8565884837/1000000000000000)
  k := 17
  n := 32
  sFloor := (1099494459837/2199023255552)
  nFloor := (1142688900295/73786976294838206464)
  eFloor := (12795630195/1152921504606846976)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell087
