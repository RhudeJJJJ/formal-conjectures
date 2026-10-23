/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell013
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (904987/70368744177664)
  b := (995485/70368744177664)
  s := [(4398046511051/4398046511104),(-9/4398046511104),(-1/2199023255552)]
  L := [(4812289718413/604462909807314587353088),(721837874347/453347182355485940514816),(18045807293/226673591177742970257408),(-1/7083549724304467820544),(1/14167099448608935641088)]
  c := (1203072429603/151115727451828646838272)
  R := (-638910828613083/50000000000000)
  total := (-2046403/125000000000000)
  k := 37
  n := 32
  sFloor := (68719476735/137438953472)
  nFloor := (1452404025695/154742504910672534362390528)
  eFloor := (1086073553941/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell013
