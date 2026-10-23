/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (538175/137438953472)
  b := (1183985/274877906944)
  s := [(4398045659135/4398046511104),(-170395/4398046511104),(-4259/2199023255552)]
  L := [(4211930409864090871287005267/41538374868278621028243970633760768),(748188979871/36893488147419103232),(18704708567/18446744073709551616),(-197/2305843009213693952),(-3/1152921504606846976)]
  c := (1870472847659/18446744073709551616)
  R := (-10065129488309/1250000000000)
  total := (-1567019289/500000000000000)
  k := 24
  n := 32
  sFloor := (2199022740111/4398046511104)
  nFloor := (869672027741/1180591620717411303424)
  eFloor := (415362844257/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell073
