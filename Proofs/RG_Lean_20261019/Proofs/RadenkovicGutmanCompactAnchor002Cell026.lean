/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (781061/17592186044416)
  b := (859167/17592186044416)
  s := [(4398046510553/4398046511104),(-109/4398046511104),(-3/2199023255552)]
  L := [(3235410259285/37778931862957161709568),(1941243669917/113336795588871485128704),(48531029615/56668397794435742564352),(-5/7083549724304467820544),(1/3541774862152233910272)]
  c := (808852564821/9444732965739290427392)
  R := (-289760771090141/25000000000000)
  total := (-51244421/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255219/4398046511104)
  nFloor := (151114232239/1208925819614629174706176)
  eFloor := (1765798224893/19342813113834066795298816)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell026
