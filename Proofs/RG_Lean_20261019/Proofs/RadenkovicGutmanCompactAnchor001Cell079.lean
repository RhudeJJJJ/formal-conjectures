/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1906817/274877906944)
  b := (1048749/137438953472)
  s := [(2199021918635/2199023255552),(-267381/2199023255552),(-6685/1099511627776)]
  L := [(91723841815/288230376151711744),(1761090121735/27670116110564327424),(44026973861/13835058055282163712),(-1477/1729382256910270464),(-17/864691128455135232)]
  c := (91723841815/288230376151711744)
  R := (-374012207301977/50000000000000)
  total := (-5155417317/1000000000000000)
  k := 22
  n := 32
  sFloor := (549755409471/1099511627776)
  nFloor := (682348924961/295147905179352825856)
  eFloor := (162947859151/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell079
