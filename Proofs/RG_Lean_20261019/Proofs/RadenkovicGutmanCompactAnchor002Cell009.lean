/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1236239/140737488355328)
  b := (679931/70368744177664)
  s := [(2199023255541/2199023255552),(-3/4398046511104),(-1/2199023255552)]
  L := [(2281414116911470225341976269/680564733841876926926749214863536422912),(810515213301/1208925819614629174706176),(60788198437/1813388729421943762059264),(1/75557863725914323419136),(-1/113336795588871485128704)]
  c := (2026302785039/604462909807314587353088)
  R := (-132106966519867/10000000000000)
  total := (-11561681/1000000000000000)
  k := 39
  n := 32
  sFloor := (1099511627769/2199023255552)
  nFloor := (757129798247/154742504910672534362390528)
  eFloor := (552950255723/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell009
