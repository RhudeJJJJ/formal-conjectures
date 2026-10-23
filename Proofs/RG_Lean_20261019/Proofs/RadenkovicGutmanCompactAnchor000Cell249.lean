/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell249
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (309211/4096)
  b := (85033/1024)
  s := [(5355920200989/4611686018427387904),(-3168851584287/9223372036854775808),(252990710839/4611686018427387904)]
  L := [(302336751437707545941691/302231454903657293676544),(-152613433/2199023255552),(533653/51539607552),(-184281/137438953472),(1655/12884901888)]
  c := (549914219597/549755813888)
  R := (14404840113/100000000000000)
  total := (597864422493/500000000000000)
  k := 0
  n := 32
  sFloor := (1006121279921/2305843009213693952)
  nFloor := 85459056867248000412430356045224458387733479312765478762169305468295908697082691584
  eFloor := 85429095120686730515188352175091044772434353476423119361639176918716053695936593920
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell249
