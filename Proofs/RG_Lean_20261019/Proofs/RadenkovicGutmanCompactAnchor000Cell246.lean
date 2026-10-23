/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell246
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (232315/4096)
  b := (511093/8192)
  s := [(3155495933095/1152921504606846976),(-1866304048125/2305843009213693952),(148947909463/1152921504606846976)]
  L := [(302417489590433200891809/302231454903657293676544),(-134598709/1099511627776),(20045611/1099511627776),(-10121/4294967296),(15489/68719476736)]
  c := (1100071521773/1099511627776)
  R := (101818203/400000000000)
  total := (1587253356523/1000000000000000)
  k := 0
  n := 32
  sFloor := (1185645909247/1152921504606846976)
  nFloor := 295476138889628615857284940870774510410085119564906454388594853330135078141952
  eFloor := 295292757792402747213659407330658547804515488077478110124176904532050260787200
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell246
