/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell000
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1/268435456)
  b := (1153433/281474976710656)
  s := [(1099511627775/1099511627776),(-3/4398046511104),(1/2199023255552)]
  L := [(182225562851/302231454903657293676544),(1749355393379/14507109835375550096474112),(5466704335/906694364710971881029632),(-17/906694364710971881029632),(1/113336795588871485128704)]
  c := (182225562851/302231454903657293676544)
  R := (-703424224267411/50000000000000)
  total := (-5222857/1000000000000000)
  k := 41
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (272354960285/309485009821345068724781056)
  eFloor := (397814866845/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell000
