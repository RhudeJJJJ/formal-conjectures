/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell030
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (571775/8796093022208)
  b := (1257905/17592186044416)
  s := [(4398046510019/4398046511104),(-27/549755813888),(-3/1099511627776)]
  L := [(1624958720843/9444732965739290427392),(1949950464493/56668397794435742564352),(48748761611/28334198897217871282176),(-7/3541774862152233910272),(1/1770887431076116955136)]
  c := (1624958720843/9444732965739290427392)
  R := (-1124162032602329/100000000000000)
  total := (-9094947/125000000000000)
  k := 33
  n := 32
  sFloor := (2199023254895/4398046511104)
  nFloor := (22360455361/75557863725914323419136)
  eFloor := (2051182282861/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell030
