/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell182
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (533649/4194304)
  b := (1174027/8388608)
  s := [(1856407303885/8796093022208),(177142687803/17592186044416),(-6137497281/8796093022208)]
  L := [(3798022822951922031809/4722366482869645213696),(-137928569473/6597069766656),(2315149909/1099511627776),(-363769/12884901888),(-421187/68719476736)]
  c := (863585372863/1099511627776)
  R := (-2415286243523/20000000000000)
  total := (-73177687273/50000000000000)
  k := 1
  n := 32
  sFloor := (1856407303885/17592186044416)
  nFloor := (1373932799005/549755813888)
  eFloor := (1112899260469/549755813888)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell182
