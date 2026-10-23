/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell146
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1104857/268435456)
  b := (607671/134217728)
  s := [(7383788124735/8796093022208),(-26716227819/1099511627776),(10832415/549755813888)]
  L := [(55243822344614985663351/604462909807314587353088),(1057286426057/70368744177664),(24819008821/105553116266496),(-135468913/4398046511104),(6170819/6597069766656)]
  c := (1607806839299/17592186044416)
  R := (-23925837899819/20000000000000)
  total := (-476180210437/1000000000000000)
  k := 4
  n := 32
  sFloor := (1792557905205/4398046511104)
  nFloor := (458913115907/562949953421312)
  eFloor := (876596114337/1125899906842624)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell146
