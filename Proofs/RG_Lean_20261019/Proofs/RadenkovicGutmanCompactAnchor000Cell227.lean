/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell227
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1215541/131072)
  b := (1337095/131072)
  s := [(1347909785231/2251799813685248),(-1549337553543/9007199254740992),(120211521891/4503599627370496)]
  L := [(9643846464562863565291/9444732965739290427392),(-17230693597/4398046511104),(3534114611/6597069766656),(-17212521/274877906944),(2244817/412316860416)]
  c := (559454985809/549755813888)
  R := (109305408161/12500000000000)
  total := (8857880205401/1000000000000000)
  k := 0
  n := 32
  sFloor := (2041362315581/9007199254740992)
  nFloor := 11977030199584976177921922374403570851119104
  eFloor := 11715709892317061656159723298548811258920960
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell227
