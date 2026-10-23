/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1153433/281474976710656)
  b := (158597/35184372088832)
  s := [(2199023255549/2199023255552),(1/4398046511104),(-1/2199023255552)]
  L := [(3908605453983/4835703278458516698824704),(781719057595/4835703278458516698824704),(58628776835/7253554917687775048237056),(-1/302231454903657293676544),(1/453347182355485940514816)]
  c := (1954302726991/2417851639229258349412352)
  R := (-1392193352049709/100000000000000)
  total := (-355319/62500000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (294915447133/309485009821345068724781056)
  eFloor := (882123326879/1237940039285380274899124224)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell001
