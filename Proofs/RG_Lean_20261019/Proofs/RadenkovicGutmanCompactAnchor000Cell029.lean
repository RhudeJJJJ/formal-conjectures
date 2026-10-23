/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1039591/17592186044416)
  b := (571775/8796093022208)
  s := [(2199023254999/2199023255552),(-55/1099511627776),(-3/1099511627776)]
  L := [(446860437973910763920324157/2658455991569831745807614120560689152),(3810157591195/113336795588871485128704),(95253847963/56668397794435742564352),(23/7083549724304467820544),(-7/3541774862152233910272)]
  c := (198445898813/1180591620717411303424)
  R := (-45013040578663/4000000000000)
  total := (-16553449/250000000000000)
  k := 33
  n := 32
  sFloor := (2199023254883/4398046511104)
  nFloor := (239572959447/1208925819614629174706176)
  eFloor := (1433176173525/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell029
