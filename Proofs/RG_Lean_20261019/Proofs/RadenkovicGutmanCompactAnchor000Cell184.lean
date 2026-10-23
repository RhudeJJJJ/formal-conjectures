/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell184
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1291429/8388608)
  b := (1420571/8388608)
  s := [(2015275930653/8796093022208),(75834440153/8796093022208),(-2148673665/2199023255552)]
  L := [(7265538392006398350627/9444732965739290427392),(-33638684527/2199023255552),(8663921705/3298534883328),(-15525067/137438953472),(-185117/206158430208)]
  c := (1663526867925/2199023255552)
  R := (-6976832981013/50000000000000)
  total := (-521902029151/250000000000000)
  k := 1
  n := 32
  sFloor := (2015275930653/17592186044416)
  nFloor := (1489865037323/274877906944)
  eFloor := (303675782043/68719476736)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell184
