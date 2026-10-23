/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell231
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (222459/16384)
  b := (978819/65536)
  s := [(7041106211927/36028797018963968),(-1027439279731/18014398509481984),(10117554065/1125899906842624)]
  L := [(9541469707296712258631/9444732965739290427392),(-25971682585/13194139533312),(1855158085/6597069766656),(-28590701/824633720832),(1309631/412316860416)]
  c := (1108883524223/1099511627776)
  R := (106094607889/25000000000000)
  total := (6313906673143/1000000000000000)
  k := 0
  n := 32
  sFloor := (331874336409/4503599627370496)
  nFloor := 6149958259742623304386355028241203291050179616885964800
  eFloor := 6085227608428483007547240187359387568468817055592742912
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell231
