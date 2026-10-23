/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (844369/140737488355328)
  b := (928805/140737488355328)
  s := [(4398046511101/4398046511104)]
  L := [(2592022755137720592356501905/10889035741470030830827987437816582766592),(920861654385/19342813113834066795298816),(69063887813/29014219670751100192948224),(7/1208925819614629174706176),(-5/1813388729421943762059264)]
  c := (575544668621/2417851639229258349412352)
  R := (-726658473654853/50000000000000)
  total := (-869019/100000000000000)
  k := 42
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (267598106227/154742504910672534362390528)
  eFloor := (511228633275/309485009821345068724781056)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell005
