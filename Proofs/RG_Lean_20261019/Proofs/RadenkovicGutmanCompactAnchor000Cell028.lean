/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (945083/17592186044416)
  b := (1039591/17592186044416)
  s := [(2199023255095/2199023255552),(-23/549755813888),(-1/549755813888)]
  L := [(184653180123700724901738965/1329227995784915872903807060280344576),(3148885422223/113336795588871485128704),(78721885675/56668397794435742564352),(-19/7083549724304467820544),(5/3541774862152233910272)]
  c := (656019878859/4722366482869645213696)
  R := (-1134857003587299/100000000000000)
  total := (-12141253/200000000000000)
  k := 33
  n := 32
  sFloor := (2199023254999/4398046511104)
  nFloor := (395988591267/2417851639229258349412352)
  eFloor := (1184443802217/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell028
