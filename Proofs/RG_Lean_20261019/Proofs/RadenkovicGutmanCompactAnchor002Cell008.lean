/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell008
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (561927/70368744177664)
  b := (1236239/140737488355328)
  s := [(2199023255543/2199023255552),(-1/1099511627776)]
  L := [(6698525938219/2417851639229258349412352),(4019101258145/7253554917687775048237056),(100477173863/3626777458843887524118528),(-5/453347182355485940514816),(1/226673591177742970257408)]
  c := (837315742277/302231454903657293676544)
  R := (-1330600650822859/100000000000000)
  total := (-10586771/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255541/4398046511104)
  nFloor := (1251455021825/309485009821345068724781056)
  eFloor := (1827935912563/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell008
