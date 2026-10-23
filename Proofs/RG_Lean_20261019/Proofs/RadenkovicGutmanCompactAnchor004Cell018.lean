/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1457487/70368744177664)
  b := (1603235/70368744177664)
  s := [(4398046510993/4398046511104),(-21/4398046511104),(-1/2199023255552)]
  L := [(5279239828455/302231454903657293676544),(395941085495/113336795588871485128704),(39593918365/226673591177742970257408),(1/7083549724304467820544),(-1/14167099448608935641088)]
  c := (1319809957113/75557863725914323419136)
  R := (-1238533842613903/100000000000000)
  total := (-255523/10000000000000)
  k := 36
  n := 32
  sFloor := (2199023255485/4398046511104)
  nFloor := (1162330636299/38685626227668133590597632)
  eFloor := (208249197767/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell018
