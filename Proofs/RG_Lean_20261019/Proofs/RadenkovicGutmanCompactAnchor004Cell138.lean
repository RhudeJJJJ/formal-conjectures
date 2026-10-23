/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell138
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (515425/268435456)
  b := (1133935/536870912)
  s := [(3680178405697/4398046511104),(-109895030835/4398046511104),(-14416233/549755813888)]
  L := [(74947015808607891093375/604462909807314587353088),(2179071960353/105553116266496),(19418384381/52776558133248),(-267251651/6597069766656),(3794431/3298534883328)]
  c := (2181245241331/17592186044416)
  R := (-5218897258419/5000000000000)
  total := (-96378561221/500000000000000)
  k := 4
  n := 32
  sFloor := (1785084022499/4398046511104)
  nFloor := (1163306151107/4503599627370496)
  eFloor := (1667508474803/9007199254740992)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell138
