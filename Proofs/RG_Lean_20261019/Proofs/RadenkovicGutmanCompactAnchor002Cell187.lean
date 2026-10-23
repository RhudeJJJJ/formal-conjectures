/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell187
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (859445/4194304)
  b := (1890779/8388608)
  s := [(2264849863199/8796093022208),(43960473321/17592186044416),(-10073957269/8796093022208)]
  L := [(3441211328276824644637/4722366482869645213696),(-410763803/3298534883328),(3004312599/1099511627776),(-101555861/412316860416),(856871/68719476736)]
  c := (400592609097/549755813888)
  R := (-15826461570653/100000000000000)
  total := (-1615718410641/500000000000000)
  k := 1
  n := 32
  sFloor := (1132424931599/8796093022208)
  nFloor := (71811136493/2147483648)
  eFloor := (1862060659077/68719476736)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell187
