/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1236239/140737488355328)
  b := (679931/70368744177664)
  s := [(4398046511079/4398046511104),(-3/4398046511104),(-1/2199023255552)]
  L := [(315952480839504390488750289/85070591730234615865843651857942052864),(1346976634387/1813388729421943762059264),(4209271333/113336795588871485128704),(1/14167099448608935641088),(-1/28334198897217871282176)]
  c := (1122488700529/302231454903657293676544)
  R := (-1315945534675373/100000000000000)
  total := (-11516671/1000000000000000)
  k := 38
  n := 32
  sFloor := (2199023255537/4398046511104)
  nFloor := (677559832359/154742504910672534362390528)
  eFloor := (506663298999/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell009
