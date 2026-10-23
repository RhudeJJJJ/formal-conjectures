/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell250
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (85033/1024)
  b := (374145/4096)
  s := [(8048970239369/9223372036854775808),(-297660884325/1152921504606846976),(47532174481/1152921504606846976)]
  L := [(151159269683190895802269/151115727451828646838272),(-378809777/6597069766656),(14135573/1649267441664),(-457837/412316860416),(10969/103079215104)]
  c := (549886812031/549755813888)
  R := (11912792441/100000000000000)
  total := (217558686519/200000000000000)
  k := 0
  n := 32
  sFloor := (755992570077/2305843009213693952)
  nFloor := 5655221119565911229109933940733625735890075636318217280441274426529327954273828339712
  eFloor := 5653582235336157486268833347145229027800520011414427572267072164867957019306948034560
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell250
