/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (586823/17592186044416)
  b := (645505/17592186044416)
  s := [(2199023255409/2199023255552),(-7/549755813888),(-1/1099511627776)]
  L := [(3423231408345/75557863725914323419136),(1026964172281/113336795588871485128704),(25673973065/56668397794435742564352),(-1/1770887431076116955136),(1/3541774862152233910272)]
  c := (427903926043/9444732965739290427392)
  R := (-1190878982270377/100000000000000)
  total := (-39562511/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255379/4398046511104)
  nFloor := (1507386241397/19342813113834066795298816)
  eFloor := (2160569226639/38685626227668133590597632)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell023
