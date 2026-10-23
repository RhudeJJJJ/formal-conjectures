/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (986957/4398046511104)
  b := (271413/1099511627776)
  s := [(549755811895/549755813888),(-3191/4398046511104),(-79/2199023255552)]
  L := [(402757231121447365086386391/166153499473114484112975882535043072),(572348388167/1180591620717411303424),(42925824041/1770887431076116955136),(-1/18446744073709551616),(1/110680464442257309696)]
  c := (89430070265/36893488147419103232)
  R := (-495946097934849/50000000000000)
  total := (-110750373/500000000000000)
  k := 29
  n := 32
  sFloor := (2199023245905/4398046511104)
  nFloor := (863712550325/302231454903657293676544)
  eFloor := (1291727842281/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell043
