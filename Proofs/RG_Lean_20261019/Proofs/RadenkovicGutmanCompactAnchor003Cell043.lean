/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (986957/4398046511104)
  b := (271413/1099511627776)
  s := [(4398046508249/4398046511104),(-143/1099511627776),(-7/1099511627776)]
  L := [(3204534173263/9444732965739290427392),(1922706865679/28334198897217871282176),(48067330595/14167099448608935641088),(-5/1770887431076116955136),(1/885443715538058477568)]
  c := (1602267086631/4722366482869645213696)
  R := (-1090207816444713/100000000000000)
  total := (-48712681/200000000000000)
  k := 32
  n := 32
  sFloor := (34359738341/68719476736)
  nFloor := (198334865735/75557863725914323419136)
  eFloor := (189723375181/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell043
