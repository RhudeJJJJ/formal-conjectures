/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (561927/70368744177664)
  b := (1236239/140737488355328)
  s := [(1099511627775/1099511627776),(1/4398046511104),(-1/2199023255552)]
  L := [(4591917116505688781811328485/10889035741470030830827987437816582766592),(611764075807/7253554917687775048237056),(7647023723/1813388729421943762059264),(7/906694364710971881029632),(-1/226673591177742970257408)]
  c := (2039220843965/4835703278458516698824704)
  R := (-1424723994716053/100000000000000)
  total := (-5669193/500000000000000)
  k := 42
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (948130815513/309485009821345068724781056)
  eFloor := (56604429565/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell008
