/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell185
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1420571/8388608)
  b := (390657/2097152)
  s := [(2187583187479/8796093022208),(56984800289/8796093022208),(-313143727/274877906944)]
  L := [(6975534850472291729245/9444732965739290427392),(-132135900845/13194139533312),(4792704179/1649267441664),(-19485749/103079215104),(1117961/206158430208)]
  c := (1608082120101/2199023255552)
  R := (-3129710478619/20000000000000)
  total := (-2612983296651/1000000000000000)
  k := 1
  n := 32
  sFloor := (2187583187479/17592186044416)
  nFloor := (1615276396853/137438953472)
  eFloor := (1315875605645/137438953472)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell185
