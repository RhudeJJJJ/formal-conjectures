/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell192
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1384143/4194304)
  b := (1522557/4194304)
  s := [(4302182265787/17592186044416),(-40452992545/4398046511104),(-624966473/2199023255552)]
  L := [(927911544985736027913/1180591620717411303424),(224391822621/8796093022208),(3096397693/4398046511104),(-116191339/549755813888),(5222631/274877906944)]
  c := (1728369938183/2199023255552)
  R := (-12041727748177/100000000000000)
  total := (-370509680693/100000000000000)
  k := 1
  n := 32
  sFloor := (2067685281911/17592186044416)
  nFloor := (1139930168471/536870912)
  eFloor := (1760735184731/1073741824)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell192
