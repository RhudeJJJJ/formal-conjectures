/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell253
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (452715/4096)
  b := (995973/8192)
  s := [(853610927279/2305843009213693952),(-252584081857/2305843009213693952),(80681653307/4611686018427387904)]
  L := [(302280697426291804984415/302231454903657293676544),(-142942963/4398046511104),(10679559/2199023255552),(-173145/274877906944),(8305/137438953472)]
  c := (17182183577/17179869184)
  R := (3367658241/50000000000000)
  total := (818675530033/1000000000000000)
  k := 0
  n := 32
  sFloor := (1282735344151/9223372036854775808)
  nFloor := 1640777207909536616409465094052133313176977273183474600584238330368176977326492432103112704
  eFloor := 1640508705229765257851839795081253283357383080590544440746308233165038538489271688892514304
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell253
