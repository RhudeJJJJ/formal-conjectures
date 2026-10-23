/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (945083/17592186044416)
  b := (1039591/17592186044416)
  s := [(4398046510363/4398046511104),(-37/1099511627776),(-1/549755813888)]
  L := [(156200246607323363558280827/1329227995784915872903807060280344576),(2663678357333/113336795588871485128704),(66591747517/56668397794435742564352),(1/7083549724304467820544),(-1/3541774862152233910272)]
  c := (1109869505507/9444732965739290427392)
  R := (-285806007739257/25000000000000)
  total := (-12231151/200000000000000)
  k := 33
  n := 32
  sFloor := (2199023255103/4398046511104)
  nFloor := (1954880430751/9671406556917033397649408)
  eFloor := (1400986152203/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell028
