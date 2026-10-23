/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (205679/17592186044416)
  b := (904987/70368744177664)
  s := [(1099511627767/1099511627776),(-5/4398046511104),(-1/2199023255552)]
  L := [(3364278149105/604462909807314587353088),(1009276084097/906694364710971881029632),(12615859051/226673591177742970257408),(-7/113336795588871485128704),(1/28334198897217871282176)]
  c := (210267384319/37778931862957161709568)
  R := (-647859818139413/50000000000000)
  total := (-75461/5000000000000)
  k := 38
  n := 32
  sFloor := (1099511627765/2199023255552)
  nFloor := (1481426754129/154742504910672534362390528)
  eFloor := (4147189323/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell012
