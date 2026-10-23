/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell250
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (85033/1024)
  b := (374145/4096)
  s := [(1006121279921/1152921504606846976),(-2381287074597/9223372036854775808),(190128697923/4611686018427387904)]
  L := [(151159269683222707286645/151115727451828646838272),(-378809777/6597069766656),(14135573/1649267441664),(-457837/412316860416),(10969/103079215104)]
  c := (549886812031/549755813888)
  R := (11912792441/100000000000000)
  total := (1087793433469/1000000000000000)
  k := 0
  n := 32
  sFloor := (755992570077/2305843009213693952)
  nFloor := 39007732680747328153531605508128136667732881389583972055620358522930744849991341061439488
  eFloor := 38996428231890501463728476969060642128510385788242318992570577469415013125888906977345536
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell250
