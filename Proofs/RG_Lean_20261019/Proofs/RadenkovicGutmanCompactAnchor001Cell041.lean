/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell041
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (203917/1099511627776)
  b := (448617/2199023255552)
  s := [(549755813649/549755813888),(-383/4398046511104),(-9/2199023255552)]
  L := [(4296663183473/18889465931478580854784),(2577972624071/56668397794435742564352),(64448683379/28334198897217871282176),(-5/3541774862152233910272),(1/1770887431076116955136)]
  c := (268541448967/1180591620717411303424)
  R := (-1110201576394923/100000000000000)
  total := (-102499911/500000000000000)
  k := 33
  n := 32
  sFloor := (2199023254395/4398046511104)
  nFloor := (998861595137/604462909807314587353088)
  eFloor := (954129786853/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell041
