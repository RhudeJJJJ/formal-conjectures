/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell135
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (387247/268435456)
  b := (851943/536870912)
  s := [(7825663740169/8796093022208),(-81424904153/4398046511104),(-38764415/137438953472)]
  L := [(24160025467762150406337/302231454903657293676544),(124757735997/8796093022208),(20985207799/52776558133248),(-50188565/2199023255552),(906179/3298534883328)]
  c := (175787321261/2199023255552)
  R := (-126324685180283/100000000000000)
  total := (-44021130379/250000000000000)
  k := 4
  n := 32
  sFloor := (1915083252325/4398046511104)
  nFloor := (1188874909371/9007199254740992)
  eFloor := (434145605621/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell135
