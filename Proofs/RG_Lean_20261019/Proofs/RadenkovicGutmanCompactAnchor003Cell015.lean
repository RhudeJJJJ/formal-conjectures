/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell015
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1095033/70368744177664)
  b := (150567/8796093022208)
  s := [(2199023255545/2199023255552),(-5/4398046511104),(1/2199023255552)]
  L := [(7889561294945/4835703278458516698824704),(4733723808179/14507109835375550096474112),(118342771019/7253554917687775048237056),(-5/906694364710971881029632),(1/453347182355485940514816)]
  c := (246548790467/151115727451828646838272)
  R := (-1357075357967189/100000000000000)
  total := (-5260637/250000000000000)
  k := 40
  n := 32
  sFloor := (2199023255543/4398046511104)
  nFloor := (488300325233/38685626227668133590597632)
  eFloor := (3649209691/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell015
