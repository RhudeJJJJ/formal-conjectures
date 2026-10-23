/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell227
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1215541/131072)
  b := (1337095/131072)
  s := [(1347909785231/2251799813685248),(-1549337553543/9007199254740992),(120211521891/4503599627370496)]
  L := [(9643846464651575881077/9444732965739290427392),(-17230693597/4398046511104),(3534114611/6597069766656),(-17212521/274877906944),(2244817/412316860416)]
  c := (1118909971629/1099511627776)
  R := (874443265779/100000000000000)
  total := (8857880209669/1000000000000000)
  k := 0
  n := 32
  sFloor := (2041362315581/9007199254740992)
  nFloor := 1053909094575502696851262974856743045969215488
  eFloor := 1030914425292975751715069284663074635976278016
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell227
