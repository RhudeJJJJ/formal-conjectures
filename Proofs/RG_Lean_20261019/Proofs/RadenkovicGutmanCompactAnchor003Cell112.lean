/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell112
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1383919/8589934592)
  b := (761155/4294967296)
  s := [(4396575825829/4398046511104),(-293979779/4398046511104),(-7331297/2199023255552)]
  L := [(110802727376308892047991109/633825300114114700748351602688),(1888817235827/54043195528445952),(47150931917/27021597764222976),(-432061/1688849860263936),(-10751/1688849860263936)]
  c := (196825182599/1125899906842624)
  R := (-108147215678227/25000000000000)
  total := (-34457056531/500000000000000)
  k := 13
  n := 32
  sFloor := (137383349483/274877906944)
  nFloor := (779929239579/576460752303423488)
  eFloor := (746065353273/576460752303423488)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell112
